/-
The running app's lifecycle on the headless twin, SQLite and real TCP:
background/surface loss, stale callbacks and arriving ops after unmount,
all-row resize, keyboard transitions, same-store restore and cold/warm
invite delivery. The subprocess companion kills a real process between
turns and restores the very same SQLite files.
-/
import Quiet
import platforms.headless.Sim
import tests.engine.Lib

open App Engine Community Data

deriving instance BEq for Text.Placed
deriving instance BEq for Row.Layout

private def freshDb (path : String) : IO Unit := do
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)

private def heldSubscriptions (l : Live) (qs : List Q) : Bool :=
  l.subs.keys.toList.all fun (k, ws, _) =>
    qs.any (fun q => (q.win default).key == k) && ws.all fun (q, w) =>
      qs.contains q && ((l.entries[q]?).map fun e => q.win e.ans == w).getD false

private def readerSubscriptions (r : Reader.St) : Bool :=
  let qs := r.deps.toList.flatMap (·.2.toList)
  r.live.entries.toList.all (fun (q, _) => qs.contains q) &&
  qs.all (fun q => r.live.entries.contains q) && heldSubscriptions r.live qs

private def subscriptions (s : St) : Bool :=
  (s.rst.map readerSubscriptions).getD true

private def settled (s : St) : IO Bool :=
  return (← s.wr.busy.get) == 0 && (← s.wr.jobs.get).isEmpty

private def scenario (dir : String) (ck : Tests.Checks) : IO Unit := do
  let path := dir ++ "/quiet.db"
  freshDb path
  let sm ← Sim.new
  sm.viewport.set #[720, 1280, 32, 24, 160]
  let initial ← App.start sm.io (← sm.viewport.get) path (some (0, true))
  let (_, s) ← (show M Unit from do
    found "Lifecycle" "Ann"
    waitIdle sm
    openPage .chat
    for i in [0:45] do
      discard <| sendText s!"message {i}: {String.ofList (List.replicate (25 + i % 5 * 30) 'a')}"
    -- The runner owns these writes; give it time to deliver notices.
    for _ in [0:100] do steps 1; IO.sleep 5
    let s ← get
    let network := s.net.isSome
    if !network then
      if (← IO.getEnv "LQ_TEST_NO_TCP") == some "1" then
        IO.println "SKIP TCP lifecycle restart: OS denied a listener (Python probe)"
      else ck.ok "TCP runner starts when a listener is permitted" false
    ck.ok "actual chat rows read and painted" (s.total == 45 && s.rows.size > 0 && s.paints > 0)
    ck.ok "exact mounted subscriptions" (subscriptions s)
    let oldReads := s.queryReads
    steps 3
    ck.ok "stable mounted queries do not reread" ((← get).queryReads == oldReads)
    sm.b.set 1800
    steps 4
    let before ← get
    let anchor := captureAnchor before
    ck.ok "non-vacuous scrolled message anchor" anchor.isSome
    sm.input.set "draft 👋 survives"
    discard <| step [.text, .ime 300]
    ck.ok "keyboard show is observed" ((← get).imeH == 300)
    for (w, h, dpi) in [(960, 720, 160), (480, 1000, 160), (720, 1280, 160), (1080, 1920, 240)] do
      let was ← get
      let a := captureAnchor was
      sm.viewport.set #[w.toUInt32, h.toUInt32, 32, 24, dpi.toUInt32]
      discard <| step [.resize, .ime 280]
      let now ← get
      ck.ok s!"{w}x{h}: simultaneous keyboard height is retained" (now.imeH == 280)
      ck.ok s!"{w}x{h}: viewport updated" (now.W == w && now.Hs == h && now.dim.dpi == dpi)
      let maxB := (bottoms now).2 - (geom now).viewNow
      let desired := a.bind fun (id, off) => (rowBottom now id).map fun bot => Lifecycle.offset (bot + heightOf now id) off
      -- Compact clumps can make a larger viewport hit the oldest edge.
      -- Preserve the anchor exactly wherever the scroll range permits it;
      -- otherwise the native scroll must clamp at that physical boundary.
      ck.ok s!"{w}x{h}: anchor preserved or clamped at the content boundary"
        (if desired.any (· > maxB) then now.b == maxB else captureAnchor now == a)
      ck.ok s!"{w}x{h}: checkpoint follows the actual clamped viewport"
        (now.mark == captureAnchor now)
      ck.ok s!"{w}x{h}: every mounted layout is current" (now.rows.toList.all fun (_, r) =>
        r.lay == Row.layout now.font now.dim now.W r.data)
      ck.ok s!"{w}x{h}: no old-width bitmap" (now.rows.toList.all fun (_, r) =>
        (r.shown.map fun b => b.w == w).getD true)
      ck.ok s!"{w}x{h}: geometry fits with keyboard" ((geom now).top + (geom now).bot + max (geom now).insetBot (geom now).ime ≤ (geom now).h)
      ck.ok s!"{w}x{h}: exact subscriptions" (subscriptions now)
    discard <| step [.ime 0]
    ck.ok "keyboard hide is observed" ((← get).imeH == 0)
    -- Capture actual scheduled work and revoke it by navigating.
    let old ← get
    let lease := old.life.lease
    let msg := old.ids[4]!.2
    openPage .home
    steps 2
    ck.ok "navigation unmounts every conversation row" ((← get).rows.isEmpty)
    ck.ok "navigation removes the old row's subscription"
      (!((← (← get).sh.plan.get).held (.row old.me.c old.me.adm msg)))
    let before ← get
    let rejected ← owned lease (do
      discard <| readRow msg
      paintRow msg
      discard <| sendText "STALE CALLBACK MUST NOT WRITE")
    let after ← get
    ck.ok "in-flight old callback is rejected" rejected.isNone
    ck.ok "old callback performs no reads, paints or writes"
      (before.queryReads == after.queryReads && before.paints == after.paints && before.out.size == after.out.size)
    -- An actual committed incoming message's notices reach the root only.
    let k := (← ((Community.currentKey after.me.c).liftL.run : SqlM SF _).run after.rd).getD .empty
    let op := sealedPost after.me.c after.me.adm after.me.dev k (← Engine.Crypto.randomBytes 24)
      "arrived after unmount".toUTF8 100 (← nowMin)
    after.wr.submit ⟨[op], false⟩
    waitIdle sm
    ck.ok "arriving message is stored" ((← Data.status after.rd op.id).isSome)
    ck.ok "arrival does not remount or paint chat" ((← get).rows.isEmpty && (← get).paints == after.paints)
    ck.ok "arrival does not re-arm the old row"
      (!((← (← get).sh.plan.get).held (.row old.me.c old.me.adm msg)))
    ck.ok "page tree subscriptions remain exact" (subscriptions (← get))
    openPage .chat
    steps 3
    ck.ok "remounted chat sees the arriving message" ((← get).ids.any (·.2 == op.id))
    ck.ok "draft survives navigation" ((← get).text == "draft 👋 survives" && (← sm.input.get) == "draft 👋 survives")
    -- Keep the scan page mounted, then remove its surface and background.
    openPage .scan
    steps 1
    ck.ok "scan mount owns a camera" (← sm.on.get)
    let n ← sm.frames.get
    let r := (← get).queryReads
    let parked := sealedPost s.me.c s.me.adm s.me.dev k (← Engine.Crypto.randomBytes 24)
      "queued while suspended".toUTF8 101 (← nowMin)
    sm.visible.set false
    discard <| step [.background, .surface false, .ime 600, .send]
    submit ⟨[parked], true⟩
    let reply := react s.me.c s.me.adm parked.id s.me.dev "👋".toUTF8 (← nowMin)
    submit ⟨[reply], true⟩
    ck.ok "suspended writes retain submission order" ((← get).toNode.toList.flatten.map (·.id) == [parked.id, reply.id])
    ck.ok "write while suspended is parked" ((← get).toNode.toList.flatten.any (·.id == parked.id))
    discard <| step [.background]
    ck.ok "repeated suspension preserves parked writes" ((← get).toNode.toList.flatten.any (·.id == parked.id))
    ck.ok "suspended write is not offered to the stopped node" ((← Data.status (← get).rd parked.id).isNone)
    steps 3
    let asleep ← get
    ck.ok "suspension stops camera and sync runner" (!(← sm.on.get) && asleep.net.isNone)
    ck.ok "suspension clears keyboard, subscriptions and tasks"
      (asleep.imeH == 0 && asleep.life.tree.isEmpty && asleep.rows.isEmpty && asleep.decoding.isNone)
    ck.ok "no read or frame without surface" (asleep.queryReads == r && (← sm.frames.get) == n)
    discard <| step [.foreground]
    ck.ok "foreground waits for surface before restarting" ((← get).net.isNone && !(← sm.on.get) && (← sm.frames.get) == n)
    sm.viewport.set #[720, 1280, 32, 24, 160]
    sm.visible.set true
    discard <| step [.surface true]
    ck.ok "resume restores viewport, sync, camera then frame"
      ((← get).W == 720 && (← sm.on.get) && (← sm.frames.get) == n + 1)
    if network then
      for _ in [0:100] do
        if (← get).net.isSome then break
        steps 1
        IO.sleep 5
      ck.ok "sync runner restarts on resume" (← pure (← get).net.isSome)
    waitIdle sm
    ck.ok "parked write reaches the resumed store owner" ((← get).toNode.isEmpty &&
      (match ← Data.status (← get).rd parked.id with | some (.valid _) => true | _ => false))
    ck.ok "dependent parked write reaches the resumed owner" (match ← Data.status (← get).rd reply.id with
      | some (.valid _) => true | _ => false)
    -- Save a real chat anchor and draft for a fresh instance.
    openPage .chat
    sm.b.set 1600
    steps 5
    sm.input.set "cold draft 🧊"
    discard <| step [.text]
    attachPhoto
    let deadline := (← IO.monoMsNow) + 5000
    while (← get).chips.isEmpty && (← IO.monoMsNow) < deadline do
      steps 1
      IO.sleep 2
    ck.ok "photo draft prepared" (!(← get).chips.isEmpty)
    sm.input.set "cold draft 🧊 at pause"
    discard <| step [.text, .background]
    ck.ok "background checkpoints the last native edit" ((← get).text == "cold draft 🧊 at pause")
    ck.ok "writer drained before suspension" (← settled (← get))).run initial
  let savedAnchor := s.mark
  let cold ← Sim.new
  cold.viewport.set (← sm.viewport.get)
  let restored ← App.start cold.io (← cold.viewport.get) path
  ck.ok "same store restores acceptance, page and anchor before first frame"
    (restored.cur == s.cur && restored.page == s.page && restored.mark == savedAnchor)
  ck.ok "same store restores composer and attachment bytes"
    (restored.text == "cold draft 🧊 at pause" && restored.chips.toList.map (·.1) == s.chips.toList.map (·.1))
  ck.ok "restore does not replay old removal notices" restored.notices.isEmpty
  let (_, restored) ← (show M Unit from do
    steps 10
    ck.ok "first layout restores the same message top" (captureAnchor (← get) == savedAnchor)
    ck.ok "restored native input equals draft" ((← cold.input.get) == "cold draft 🧊 at pause")
    ck.ok "restored subscriptions are exact" (subscriptions (← get))
    -- A removal confirmation is durable, but restoration never confirms it.
    let u := "target".toUTF8
    modify fun s => { s with profileOf := some (u, "Target", false), removal := .second u }
    openPage .removeConfirm
    steps 1
    discard <| step [.background]).run restored
  let removal ← App.start cold.io (← cold.viewport.get) path
  ck.ok "pending removal restores at the same confirmation"
    (removal.page == .removeConfirm && removal.removal == restored.removal && removal.profileOf == restored.profileOf)
  ck.ok "restore never issues a removal" (← settled removal)
  -- Different community drafts are keyed by acceptance.
  let (_, switched) ← (show M Unit from do
    steps 1
    let first := (← get).cur
    found "Second" "Ann"
    waitIdle cold
    sm.input.set "unused"
    modify fun s => { s with text := "second draft" }
    switchToAcc first
    ck.ok "acceptance switch restores first draft" ((← get).text == "cold draft 🧊 at pause")
    let second := ((← get).comms.find? (·.acc != first)).get!
    switchToAcc second.acc
    ck.ok "acceptance switch restores second draft" ((← get).text == "second draft")
    discard <| step [.background]).run removal
  -- Cold and warm links use the same production parser, without a session.
  let bearer ← Chaos.freshSeed "link"
  let some (_, invite) ← ((Community.inviteTo switched.me.c switched.me.adm switched.me.dev bearer []).liftL.run : SqlM SF _).run switched.rd
    | throw (IO.userError "fixture has no node key")
  let linkPath := dir ++ "/link.db"
  freshDb linkPath
  let linkSim ← Sim.new
  linkSim.urls.set #[invite.text]
  let linkStart ← App.start linkSim.io (← linkSim.viewport.get) linkPath
  let (_, joining) ← (show M Unit from do
    steps 1
    ck.ok "cold link opens name without a session" ((← get).page == .name && (← get).net.isNone &&
      ((← get).invite.map (·.text)) == some invite.text)
    linkSim.input.set "New member"
    discard <| step [.text]
    onPageAct .continue_
    steps 1
    ck.ok "invite draft reaches agree" ((← get).page == .agree && (← get).joinName == "New member")
    discard <| step [.background]).run linkStart
  let rejoin ← App.start linkSim.io (← linkSim.viewport.get) linkPath
  ck.ok "unsubmitted join flow survives restore" (rejoin.page == joining.page && rejoin.joinName == joining.joinName &&
    (rejoin.invite.map (·.text)) == some invite.text)
  let (_, waiting) ← (show M Unit from do
    steps 1
    onPageAct .agree
    waitIdle linkSim
    ck.ok "join request waits for actual admission" ((← get).page == .waiting && (← get).me.waiting)
    discard <| step [.background]).run rejoin
  let pending ← App.start linkSim.io (← linkSim.viewport.get) linkPath
  ck.ok "pending join survives restore" (pending.page == .waiting && pending.cur == waiting.cur && pending.me.waiting)
  let (_, _) ← (show M Unit from do
    steps 1
    linkSim.urls.set #[invite.text]
    steps 1
    ck.ok "warm link selects the held acceptance without a second join" ((← get).cur == pending.cur && (← get).comms.size == 1)
    let old := (← get).cur
    linkSim.urls.set #["quiet://join/not-valid"]
    steps 1
    ck.ok "malformed link preserves selection" ((← get).cur == old && (← get).comms.size == 1)
    discard <| step [.background]).run pending
  -- Removal stored while the app is dead: start must neither select the
  -- removed acceptance nor announce a removal it had not observed live.
  let gone := Community.remove switched.me.c switched.me.adm switched.me.c switched.me.adm switched.me.dev
  switched.wr.submit ⟨[gone], false⟩
  while (← switched.wr.busy.get) > 0 do IO.sleep 1
  let afterRemoval ← App.start cold.io (← cold.viewport.get) path
  ck.ok "stored removal is valid before cold start" (match ← Data.status afterRemoval.rd gone.id with
    | some (.valid _) => true | _ => false)
  ck.ok "cold start does not select a removed acceptance" (afterRemoval.cur != switched.cur &&
    !(afterRemoval.comms.any (·.acc == switched.cur)))
  ck.ok "cold start records stored removal without announcing it"
    (afterRemoval.goneSeen.contains switched.cur && afterRemoval.notices.isEmpty)

/-- The real Reader.pass, paused between sampling its request and opening
SQLite, while another thread publishes a new window. A torn old-wants /
new-generation pair would permanently consume the new generation without
ever reading its window, even on the periodic journal fallback. -/
private def readerRequest (dir : String) (ck : Tests.Checks) : IO Unit := do
  let path := dir ++ "/reader-request.db"
  freshDb path
  let db ← openDb path
  db.filings
  let d := Device.named "reader request snapshot"
  let r := root d (Tests.keyOf d)
  let k := sha256 "reader request key".toUTF8
  let msg := sealedPost r.id r.id d k (ByteArray.mk (Array.replicate 24 7))
    "a committed message before navigation".toUTF8 1 1234
  (receive fam (intake fam true [r, contentKey r.id k, msg])).run db
  let commits ← IO.mkRef 1
  let sh ← Reader.Shared.new commits
  let countW := Reader.Want.count r.id none
  let windowW := Reader.Want.window r.id none 100 100
  sh.setWants #[countW]
  let (_, initial) ← (Reader.pass sh).run { rd := ← openDb path }
  ck.ok "request fixture has a real count and no window"
    (((← sh.board.get).get? countW).map (·.1) == some (.count 0 1) &&
      ((← sh.board.get).get? windowW).isNone)
  let sampled ← IO.mkRef false
  let release ← IO.mkRef false
  let await (flag : IO.Ref Bool) : IO Unit := do
    let deadline := (← IO.monoMsNow) + 5000
    while !(← flag.get) do
      if (← IO.monoMsNow) ≥ deadline then throw (IO.userError "reader request barrier timed out")
      IO.sleep 1
  let pending ← IO.asTask (prio := .dedicated) do
    (Reader.pass sh (afterSnapshot := do sampled.set true; await release)).run initial
  try
    await sampled
    sh.setWants #[windowW, countW]
  finally
    release.set true
  let (_, sampledState) ← match ← IO.wait pending with
    | .ok result => pure result
    | .error e => throw e
  ck.ok "sampled request keeps its original generation" (sampledState.gen == initial.gen)
  -- No commit, note, further request, or arbitrary sleep repairs the state.
  let (_, next) ← (Reader.pass sh).run sampledState
  let expected : Reader.Val := .window #[(msgKey 1 1234, msg.id)] 0
  ck.ok "new window arrives on next pass without another change"
    (((← sh.board.get).get? windowW).map (·.1) == some expected &&
      next.gen == (← sh.generation))
  let (_, fallback) ← (Reader.pass sh).run { next with readAt := 0 }
  ck.ok "periodic fallback retains the requested message window"
    (((← sh.board.get).get? windowW).map (·.1) == some expected &&
      fallback.wantSet.contains windowW)
  ck.ok "request regression performs no intervening writes or notifications"
    ((← commits.get) == 1 && (← sh.notes.get).isEmpty && fallback.seen == initial.seen)

private def threaded (dir : String) (ck : Tests.Checks) : IO Unit := do
  let path := dir ++ "/reader.db"
  freshDb path
  let sm ← Sim.new
  let s ← App.start sm.io (← sm.viewport.get) path
  let (_, _) ← (show M Unit from do
    found "Reader" "Ann"
    waitIdle sm
    openPage .chat
    discard <| sendText "reader-owned message"
    waitIdle sm
    set (← spawnReader (← get))
    for _ in [0:30] do steps 1; IO.sleep 2
    let s ← get
    ck.ok "production reader is running" (s.reader.isSome && s.rst.isNone)
    let worker := s.reader
    let pic : Row.Pic := { hash := "waiting-picture".toUTF8, w := 1, h := 1, chunks := [s.ids[0]!.2] }
    discard <| image { pic with got := 1, total := 1 } 1 1
      (Raster.pictureOwner s.me.c s.ids[0]!.2 pic.attachment)
    ck.ok "picture teardown has live requests to remove" (!(← get).pictureNeeds.isEmpty)
    openPage .home
    IO.sleep 10
    ck.ok "unmount joins the in-flight reader" (← match worker with
      | some w => IO.hasFinished w.done | none => pure false)
    ck.ok "unmount drops reader wants and board" ((← s.sh.wants).isEmpty &&
      ((← s.sh.board.get).get? (.row s.me.c s.me.adm s.ids[0]!.2)).isNone)
    ck.ok "unmount drops every picture request" ((← get).pictureNeeds.isEmpty && (← get).rasterNeeds.isEmpty &&
      (← get).imgWaiting.isEmpty && (← get).imgs.isEmpty)
    openPage .chat
    for _ in [0:30] do steps 1; IO.sleep 2
    ck.ok "remount restarts the reader and repopulates rows" ((← get).reader.isSome && !(← get).rows.isEmpty)
    -- Each navigation starts a real dedicated reader. Its initial request
    -- and subsequent row request must both populate the actual chat viewport.
    for cycle in [0:12] do
      openPage .home
      steps 1
      openPage .chat
      let start ← IO.monoMsNow
      while (← get).rows.isEmpty && (← IO.monoMsNow) < start + 2000 do
        steps 1
        IO.sleep 2
      let live ← get
      ck.ok s!"threaded navigation {cycle}: message window arrives" (live.total == 1 &&
        live.ids.size == 1 && live.rows.size == 1 && live.reader.isSome)
    discard <| step [.background]
    ck.ok "background joins reader and clears its board" ((← get).reader.isNone && (← s.sh.wants).isEmpty)
    discard <| step [.foreground]
    for _ in [0:30] do steps 1; IO.sleep 2
    ck.ok "foreground restarts production reader" ((← get).reader.isSome && !(← get).rows.isEmpty)
    sm.cmds.modify (·.push "chaos 3")
    steps 1
    discard <| step [.background]
    ck.ok "suspend drains an in-flight write producer" ((← get).chaos.isNone && (← (← get).wr.busy.get) == 0)
    discard <| step [.foreground]
    waitIdle sm
    ck.ok "producer writes survive suspend" ((← get).total ≥ 3)
    modify fun s => { s with
      mark := some ("no-longer-readable".toUTF8, 20),
      anchor := some (.empty, "no-longer-readable".toUTF8), restoreAnchor := true }
    for _ in [0:50] do steps 1; IO.sleep 2
    ck.ok "unreadable restored anchor falls back to newest" ((← get).mark.isNone && (← get).b == 0 && !(← get).restoreAnchor)
    -- Even an unchanged completed window must resolve a missing anchor.
    waitIdle sm
    modify fun s => { s with mark := some ("still-unreadable".toUTF8, 20), restoreAnchor := true }
    for _ in [0:10] do steps 1; IO.sleep 2
    ck.ok "unchanged reader window resolves an unreadable anchor" ((← get).mark.isNone && !(← get).restoreAnchor)
    discard <| step [.background]).run s

/-- Subprocess mode: persist input while the writer is intentionally
paused. The parent sends SIGKILL after READY, then invokes verify. -/
private def crash (mode dir : String) : IO Unit := do
  let sm ← Sim.new
  let path := dir ++ "/crash.db"
  if mode == "crash" then freshDb path
  let s ← App.start sm.io (← sm.viewport.get) path
  let (_, _) ← (show M Unit from do
    if mode == "crash" then
      found "Crash" "Ann"
      waitIdle sm
      openPage .chat
      -- Short messages now share one compact clump. Use multiline content
      -- so this exercises a real scroll anchor even at phone density.
      for i in [0:20] do discard <| sendText s!"crash anchor message {i}\nsecond line\nthird line\nfourth line"
      waitIdle sm
      sm.b.set 1500
      steps 4
      unless (captureAnchor (← get)).isSome do
        throw (IO.userError "crash fixture must have a nonempty scrolled anchor")
      sm.input.set "durable before kill"
      discard <| step [.text]
      (← get).wr.paused.set true
      discard <| sendText "queued before kill"
      saveCheckpoint
      -- the writer's thread commits it (paused for jobs, not checkpoints)
      while !(← (← get).wr.saveDone) do IO.sleep 1
      IO.FS.writeBinFile (dir ++ "/expected.bin") (Codec.encode (checkpoint (← get)))
      IO.println "READY"
      (← IO.getStdout).flush
      while true do IO.sleep 100
    else
      let ck ← Tests.Checks.new
      ck.ok "SIGKILL restores page and composer" ((← get).page == .chat && (← get).text == "durable before kill")
      let expected := (Lifecycle.restore (← IO.FS.readBinFile (dir ++ "/expected.bin"))).get!
      let expectedAnchor := some (expected.2.2.2.1, expected.2.2.2.2.1)
      ck.ok "SIGKILL restores the saved nonempty anchor" ((← get).mark == expectedAnchor &&
        !expected.2.2.2.1.isEmpty)
      steps 8
      ck.ok "SIGKILL anchor survives first layout and queued arrival" (captureAnchor (← get) == expectedAnchor)
      ck.ok "SIGKILL replays journaled write exactly once" ((← get).total == 21)
      IO.Process.exit (← ck.finish "lifecycle crash").toUInt8).run s

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/lifecycle"
  IO.FS.createDirAll dir
  if args[1]? == some "reader-request" then
    let ck ← Tests.Checks.new
    readerRequest dir ck
    return ← ck.finish "reader request"
  if let some mode := args[1]? then crash mode dir; return 0
  let ck ← Tests.Checks.new
  try
    scenario dir ck
    readerRequest dir ck
    threaded dir ck
  catch e => IO.eprintln s!"lifecycle exception: {e}"; IO.Process.exit 1
  IO.Process.exit (← ck.finish "lifecycle").toUInt8
