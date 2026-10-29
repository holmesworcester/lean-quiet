/- Attachment children of one tall message mount and unmount while their
parent remains visible. Signed ops, SQLite and the real App.step. -/
import platforms.headless.Sim
import tests.engine.Checks

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

end Components

def main (args : List String) : IO Unit := do
  let ck ← Checks.new
  Components.run (args.headD "out/components") ck
  let code ← ck.finish "op-components"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
