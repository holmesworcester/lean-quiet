/- Attachment children of one tall message mount and unmount while their
parent remains visible. Signed ops, SQLite and the real App.step. -/
import platforms.headless.Sim
import tests.engine.Checks
import tests.engine.Lib

open App Engine Community Data Tests

namespace Components

def run (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/quiet.db" ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  sm.viewport.set #[1080, 1100, 32, 24, 420]
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let ((), final) ← (show M Unit from do
    sm.cmds.modify (·.push "found components|Ann")
    steps 3
    waitIdle sm
    sm.cmds.modify (·.push "channel")
    steps 2
    for _ in [0:4] do sm.cmds.modify (·.push "photo"); steps 2
    let text := String.intercalate " " (List.replicate 150 "A message owns its text.")
    sm.cmds.modify (·.push s!"post {text}")
    waitIdle sm
    let s ← get
    let some (_, message) := s.ids[0]? | throw (IO.userError "fixture message missing")
    let some row := s.rows[message]? | throw (IO.userError "fixture row missing")
    ck.ok "fixture is one real message with four attachment ops" (s.ids.size == 1 && row.data.pics.length == 4)
    let rowWant := Reader.Want.row s.me.c s.me.adm message
    let before ← s.sh.plan.get
    let some rs := s.rst | throw (IO.userError "headless reader missing")
    ck.ok "message query owns only its message fact and content key"
      ((rs.deps.getD rowWant #[]).size == 2 &&
        (rs.deps.getD rowWant #[]).contains (Q.get message))
    ck.ok "attachments supply their own opened size metadata"
      (row.data.pics.all fun p => p.w > 0 && p.h > 0 && !p.key.isEmpty)
    -- A real remount with a delayed metadata answer must not publish a
    -- text-only height. This is the geometry race seen during fast flings.
    let board ← s.sh.board.get
    let p := row.data.pics.head!
    let pendingBoard := (board.keep fun w => w != .attachment s.me.c p.attachment)
      |>.put (.attachments s.me.c message) (.ids [p.attachment])
      |>.put (.emojis s.me.c message) (.emojis [])
    s.sh.board.set pendingBoard
    modify fun s => { s with rows := s.rows.erase message }
    mount pendingBoard message
    ck.ok "a cold message waits for attachment size before choosing its height"
      (!(← get).rows.contains message)
    let complete := pendingBoard.put (.attachment s.me.c p.attachment) (.picture (some p))
    s.sh.board.set complete
    mount complete message
    ck.ok "metadata alone establishes image geometry without decoding pixels"
      ((← get).rows[message]?.any fun r => r.lay.pics.size == 1 && r.shown.isNone)
    s.sh.board.set board
    set s
    ck.ok "offscreen author does not subscribe just because its message is mounted"
      (!before.held (.author s.me.c s.me.user))
    let active := s.pictureNeeds.toList
    ck.ok "visible picture components declare their own slice queries" (!active.isEmpty)
    ck.ok "picture ownership names its attachment op type and identity"
      (active.all fun n => row.data.pics.any fun p =>
        n.owner == Raster.pictureOwner s.me.c message p.attachment &&
          (n.key == .slices p.chunks || n.key == .picture s.me.c p.attachment))
    -- The original image horizon remains useful beyond 512 px, while
    -- the larger text buffer must not silently double image demand.
    let rowBottom := (bottoms s).1[0]!
    let pictureTop := row.lay.pics.foldl (fun top bx => max top (rowBottom + row.lay.h - bx.y)) 0
    sm.b.set (pictureTop + 768).toFloat
    steps 8
    ck.ok "images 768px beyond the viewport retain their original prefetch demand"
      (!(← get).pictureNeeds.isEmpty && (← get).rows.contains message)
    sm.b.set (pictureTop + 1536).toFloat
    steps 8
    ck.ok "the extended text buffer does not extend image queries past 1024px"
      ((← get).pictureNeeds.isEmpty && (← get).rows.contains message)
    -- Move from the pictures at the bottom to the text at the top, in
    -- the same row. The row cannot unmount to make this test pass.
    sm.b.set (← sm.maxB.get)
    steps 8
    let after ← get
    let plan ← after.sh.plan.get
    ck.ok "scrolling within a tall message retains the message's query ticket"
      (plan.ticket rowWant == before.ticket rowWant && after.rows.contains message)
    ck.ok "offscreen attachment children release every chunk query"
      (after.pictureNeeds.isEmpty && active.all fun n => !plan.held n.key)
    ck.ok "offscreen attachment children retain no queued decode or bitmap handle" after.imgs.isEmpty
    let some reader := after.rst | throw (IO.userError "test reader missing")
    ck.ok "offscreen child subscriptions and reverse-index entries are released"
      (active.all (fun n => !reader.deps.contains n.key) &&
        reader.rev.toList.all (fun (_, wants) => wants.all reader.wantSet.contains))
    sm.b.set 0
    steps 12
    let returned ← get
    ck.ok "returning to pictures remounts their owned queries" (!returned.pictureNeeds.isEmpty)
    ck.ok "the message ticket survives both viewport changes"
      ((← returned.sh.plan.get).ticket rowWant == before.ticket rowWant)
    let mut finished := false
    let deadline := (← IO.monoMsNow) + 5000
    while !finished && (← IO.monoMsNow) < deadline do
      steps 1
      IO.sleep 2
      for (_, h) in (← get).imgs.toList do
        if (← h.value).isSome then finished := true
    ck.ok "returning pictures finish through the shared worker" finished
    openPage .home
    steps 2
    ck.ok "page unmount drops the component demand tree"
      ((← get).pictureNeeds.isEmpty && (← get).rasterNeeds.isEmpty)
    ).run initial
  final.raster.reconcile []

/-- Real signed ops exercise list→set→emoji and shared author ownership,
including pending writes, duplicate reactions and unrelated invalidation. -/
def children (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/quiet.db" ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let (_, final) ← (show M Unit from do
    found "child queries" "Ann"
    openPage .chat
    discard <| sendText "First message"
    let me := (← get).me
    let some key ← intentView (Community.currentKey me.c) | throw (IO.userError "fixture key missing")
    let w ← intentView (Community.send me.c me.adm me.dev key (← newBytes 24)
      "Second message".toUTF8 ((← nowMin) + 5))
    discard <| writeAll w
    waitIdle sm
    let s ← get
    let msg := s.ids[0]!.2
    let rowWant := Reader.Want.row s.me.c s.me.adm msg
    let authorWant := Reader.Want.author s.me.c s.me.user
    let board ← s.sh.board.get
    let rowVersion := (board.get? rowWant).map (·.2)
    let plan ← s.sh.plan.get
    ck.ok "two message headers share one author query with two owners"
      ((plan.needs.filter (·.key == authorWant)).length == 2)
    ck.ok "both headers display their author component's result"
      (s.rows.size == 2 && s.rows.toList.all (fun (_, r) => r.data.name == "Ann"))
    discard <| reactTo msg "❤️"
    waitIdle sm
    let s ← get
    let block := Reader.Want.emojis s.me.c msg
    let heart := Reader.Want.reaction s.me.c msg s.me.user "❤️"
    let board ← s.sh.board.get
    let blockVersion := (board.get? block).map (·.2)
    let heartVersion := (board.get? heart).map (·.2)
    ck.ok "reaction block discovers the emoji and the pill owns its count"
      ((board.get? block).any (fun (v, _) => v == .emojis ["❤️"]) &&
       (board.get? heart).any (fun (v, _) => v == .reaction ⟨"❤️", 1, true⟩))
    let bob := Device.named "component Bob"
    let bearer := Device.named "component bearer"
    let inv := invite s.me.c s.me.adm s.me.dev bearer.pk false
    let req := request s.me.c inv.id bob (Tests.keyOf bob) bearer.sk
    let approval := approve s.me.c req.id s.me.adm s.me.dev
    let adm := admit s.me.c req.id [approval.id]
    let now ← nowMin
    let reaction := react s.me.c adm.id msg bob "❤️".toUTF8 (now + 1)
    s.wr.paused.set true
    ck.ok "second reactor's signed pending write is accepted"
      (← writeAll ⟨[inv, req, approval, adm, reaction]⟩)
    steps 12
    let changed ← get
    let board ← changed.sh.board.get
    ck.ok "pending reaction updates its own count without waiting for SQLite commit"
      ((board.get? heart).any (fun (v, _) => v == .reaction ⟨"❤️", 2, true⟩))
    ck.ok "same emoji leaves the block's distinct-set answer unchanged"
      ((board.get? block).map (·.2) == blockVersion)
    ck.ok "reaction update does not rerun or republish the message's own query"
      ((board.get? rowWant).map (·.2) == rowVersion)
    ck.ok "changed count publishes a new pill version"
      ((board.get? heart).map (·.2) != heartVersion)
    discard <| write (react s.me.c adm.id msg bob "❤️".toUTF8 (now + 2))
    steps 12
    let board ← (← get).sh.board.get
    ck.ok "duplicate reaction ops by one person still count once"
      ((board.get? heart).any (fun (v, _) => v == .reaction ⟨"❤️", 2, true⟩))
    s.wr.paused.set false
    waitIdle sm
    discard <| write (profile s.me.c s.me.adm s.me.dev "Renamed Ann".toUTF8 (now + 10))
    waitIdle sm
    let renamed ← get
    ck.ok "profile update refreshes every mounted author component"
      (renamed.rows.toList.all (fun (_, r) => r.data.name == "Renamed Ann"))
    ck.ok "profile update leaves the message query version alone"
      (((← renamed.sh.board.get).get? rowWant).map (·.2) == rowVersion)
    let some reader := renamed.rst | throw (IO.userError "reader missing")
    ck.ok "emoji pill subscribes only to its indexed reactor set"
      ((reader.deps.getD heart #[]) == #[.list (Community.react.byMessageEmoji.query
        [s.me.c, msg, "❤️".toUTF8] (desc := false))])
    let q := Q.list (Community.message.all.query [s.me.c] (limit := some 1))
    let before ← q.run s.rd (← get).out
    s.wr.paused.set true
    let some key ← intentView (Community.currentKey s.me.c)
      | throw (IO.userError "fixture key missing")
    let old := Community.sealedPost s.me.c s.me.adm s.me.dev key (← newBytes 24)
      "An old backfill outside the window".toUTF8 0 now
    ck.ok "signed old backfill is accepted while the writer is paused" (← write old)
    let pending ← q.run s.rd (← get).out
    ck.ok "an out-of-window pending row cannot change a bounded answer's pending flags"
      (pending == before)
    s.wr.paused.set false
    waitIdle sm
    ck.ok "committing the out-of-window backfill leaves the bounded answer unchanged"
      ((← q.run s.rd (← get).out) == before)
    openPage .home
    steps 5
    let plan ← (← get).sh.plan.get
    ck.ok "leaving chat releases the block and every reaction pill"
      (!plan.held block && !plan.held heart && !plan.held rowWant)
    ).run initial
  final.raster.reconcile []

end Components

def main (args : List String) : IO Unit := do
  let ck ← Checks.new
  Components.run (args.headD "out/components") ck
  Components.children ((args.headD "out/components") ++ "-children") ck
  let code ← ck.finish "op-components"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
