/- Accepted local operations outlive an actual failed Runner. The first
signed write commits before a gated production hook throws; a second is
already in the real channel, and a third arrives after failure. Native stop
is held on the real closing mutex while App stages and local commits run. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open App Engine Engine.Sync Data Tests

namespace AppRunnerFailure

def waitFor (ms : Nat) (ready : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← ready then return true
    IO.sleep 1
  return ← ready

def stored (db : Db) (op : Op) : IO Bool := PublicationFixture.valid db op

def checkStage (state : App.St) : IO App.St := do
  return (← (App.step []).run state).2

/-- Test-only SDK ownership gate. It pauses actual queue admission, not a
substitute Writer. The taken value is restored exactly once in cleanup. -/
structure QueueGate where
  writer : Writer
  held : IO.Ref (Option WriterQueue)

def QueueGate.release (gate : QueueGate) : IO Unit := do
  let previous ← gate.held.modifyGet fun value => (value, none)
  if let some queue := previous then gate.writer.jobs.set queue

/-- A bad eager admission increments actual busy before waiting on the
held jobs ref. Release that mutation deterministically after observing it;
neither a process timeout nor an unscheduled task counts as rejection. -/
def stage (t : Checks) (gate : QueueGate) (label : String) (action : App.M Unit)
    (state : App.St) : IO App.St := do
  let task ← IO.asTask (prio := .dedicated) (action.run state)
  let observed ← waitFor 2000 do
    return (← IO.hasFinished task) || (← gate.writer.busy.get) > 1
  unless observed do
    gate.release
    throw (IO.userError "UI stage reached neither completion nor actual second queue admission")
  let completed ← IO.hasFinished task
  t.ok label completed
  unless completed do gate.release
  let .ok (_, state) ← IO.wait task | throw (IO.userError "unexpected guarded App stage failure")
  return state

unsafe def run (dir : String) (t : Checks) (mode : Nat) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let initial ← App.start sm.io (← sm.viewport.get) path
  let initial ← checkStage initial
  let initial ← checkStage initial
  let db ← openDb path
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let armed ← IO.mkRef true
  let hooks := Connection.hooks fam Connection.sodium .empty
  let x : Sync SF (SqlM SF) := { fam, hooks := { hooks with react := do
    if ← armed.modifyGet (fun value => (value, false)) then
      entered.resolve ()
      discard <| IO.wait release.result?
      throw (IO.userError "expected AppRunnerFailure post-commit hook failure")
    hooks.react } }
  let r ← Runner.start x db 0 0 (cfg := { queue := 2 })
  let stopHeld ← IO.Promise.new
  let releaseStop ← IO.Promise.new
  let stopOwner ← IO.asTask (prio := .dedicated) do
    r.closing.atomically do
      stopHeld.resolve ()
      discard <| IO.wait releaseStop.result?
  discard <| IO.wait stopHeld.result?
  let first := PublicationFixture.root "committed before runner failure"
  let second := PublicationFixture.root "accepted only by failed runner channel"
  let third := PublicationFixture.root "new local action after runner failure"
  let mut state := { initial with netCfg := some (0, true) }
  state := (← (App.attachNetwork none (some r)).run state).2
  let held ← IO.mkRef (none : Option WriterQueue)
  let gate : QueueGate := ⟨initial.wr, held⟩
  try
    state := (← (App.submit ⟨[first], true⟩).run state).2
    unless ← waitFor 2000 entered.isResolved do
      throw (IO.userError "actual first write did not reach failure hook")
    t.ok "real runner commits the first signed op before its gated hook fails"
      (← stored state.rd first)
    state := (← (App.submit ⟨[second], true⟩).run state).2
    let journaled ← waitFor 2000 state.wr.saveDone
    let cp ← Lifecycle.load state.rd
    let durable := cp.bind fun cp =>
      (Codec.decode (cp.2.2.2.2.2[10]?.getD .empty) : Option (List ByteArray))
    t.ok "already admitted channel work remains in the actual durable App journal"
      (journaled && state.toNode.isEmpty && !(← stored state.rd second) &&
        (durable.getD []).contains first.bytes && (durable.getD []).contains second.bytes)
    -- Pause the actual writer, then take the actual SDK ref token. Its
    -- checkpoint path remains live and neither task can overwrite the queue.
    state.wr.setPaused true
    let taken ← state.wr.jobs.take
    held.modify (fun _ => some taken)
    release.resolve ()
    unless ← waitFor 2000 (IO.hasFinished r.done) do
      throw (IO.userError "actual runner did not report failure")
    t.ok "real handler error finishes Runner.done without closing its write channel"
      (!r.done.get.isOk && !(← r.writes.isClosed))
    -- This path must detect failure even though successful channel admission
    -- removed all old jobs from toNode. It must not join held App-owned stop call.
    state ← if mode == 0 then (fun result => result.2) <$> App.flushNode.run state
      else if mode == 1 then (fun result => result.2) <$> App.netStep.run state
      else (fun result => result.2) <$> (App.suspend 150).run state
    let detected := state.net.isNone && state.netCfg.isNone
    t.ok "entry stage detects the finished runner even with an empty parked queue" detected
    unless detected do return
    t.ok "App reports an actual sync failure notice"
      (state.notices.any (·.startsWith "Sync stopped"))
    t.ok "failed teardown does not use the normal-stop slot that parks later writes"
      (state.netStop.isNone && !(← IO.hasFinished stopOwner))
    unless state.netStop.isNone do return
    t.ok "failed teardown retains its actual unfinished task"
      (state.failedNetStop.isSome && !(← state.failedNetStop.mapM (fun task => liftM (IO.hasFinished task))).getD true)
    if let some task := state.netReplay then
      unless ← waitFor 2000 (do return (← state.wr.busy.get) == 1 || (← IO.hasFinished task)) do
        throw (IO.userError "replay reached neither queue admission nor completion")
    let replayBlocked := (← state.wr.busy.get) == 1 && state.netReplay.isSome &&
      !(← state.netReplay.mapM (fun task => liftM (IO.hasFinished task))).getD true
    t.ok "replay reaches real queue admission off the App thread" replayBlocked
    -- A compiled control that omits replay must terminate too. Its observed
    -- missing admission already fails above; do not leave unrelated work
    -- waiting on a gate that no longer has the expected first producer.
    t.ok "accepted journal remains owned while actual replay admission is blocked"
      (state.queuedWrites.contains second.bytes && !(← stored state.rd second))
    unless replayBlocked do return
    state ← stage t gate "new action parks without a second actual writer admission"
      (App.submit ⟨[third], true⟩) state
    t.ok "later local action remains parked until replay submission is observed"
      (state.toNode.toList.flatten.any (·.id == third.id))
    if state.toNode.isEmpty then return
    state := (← App.netStep.run state).2
    t.ok "next network stage cannot reinstall or restart the failed runner"
      (state.net.isNone && state.netBoot.isNone && state.netCfg.isNone)
    let before ← sm.frames.get
    for _ in [:3] do
      state ← stage t gate "active frame does not wait on held replay admission"
        (discard <| App.step []) state
    t.ok "actual App stages keep publishing while failed teardown is held"
      ((← sm.frames.get) ≥ before + 3 && !(← IO.hasFinished stopOwner))
    t.ok "the published App frame carries the sync failure notice"
      (state.noticeClock.any (fun n => n.1.startsWith "Sync stopped"))
    gate.release
    if let some task := state.netReplay then
      unless ← waitFor 2000 (IO.hasFinished task) do
        throw (IO.userError "released actual replay admission did not finish")
    state ← checkStage state
    if mode < 2 then
      let queue ← state.wr.jobs.get
      let queuedIds := (queue.writes ++ queue.events).flatMap fun job => job.ops.map (·.id)
      t.ok "actual Writer queue preserves journal replay before the later accepted action"
        (queuedIds == [first.id, second.id, third.id])
    state.wr.setPaused false
    let recovered ← waitFor 3000 do
      return (← stored state.rd second) && (← stored state.rd third)
    t.ok "journal replay and a later action commit locally while the App-owned stop call remains pending"
      (recovered && !(← IO.hasFinished stopOwner))
    let held ← r.writes.tryRecv
    let extra ← r.writes.tryRecv
    t.ok "App never offers the later action into the already finished runner"
      (held.any (fun ops => ops.map (·.id) == [second.id]) && extra.isNone)
    let rows ← state.rd.query "SELECT id FROM catalog ORDER BY seq" #[]
    let ids := rows.toList.filterMap (·[0]?)
    t.ok "all accepted ops have exactly one catalog entry after recovery"
      ([first, second, third].all fun op => (ids.filter (· == op.id)).length == 1)
    t.ok "local replay preserves accepted write order ahead of the later action"
      (ids.filter (fun id => [first.id, second.id, third.id].contains id) ==
        [first.id, second.id, third.id])
    state ← checkStage state
    t.ok "accepted journal entries are cleared only after the App observes stored ops"
      (state.queuedWrites.isEmpty)
    releaseStop.resolve ()
    discard <| IO.wait stopOwner
    if let some task := state.failedNetStop then
      unless ← waitFor 2000 (IO.hasFinished task) do
        throw (IO.userError "released recovery teardown did not complete")
    t.ok "the retained recovery task actually stops its failed runner"
      ((← r.stopped.get) && (← IO.hasFinished r.listening))
    state := (← App.pollRetired.run state).2
    t.ok "lifecycle polling releases completed replay and failed teardown handles"
      (state.netReplay.isNone && state.failedNetStop.isNone)
  finally
    gate.release
    initial.wr.setPaused false
    release.resolve ()
    releaseStop.resolve ()
    discard <| IO.wait stopOwner
    r.stop
  -- App.start owns continuing writer/pruner workers; main exits explicitly.
  t.ok "actual failed runner listener cleanup completes after its gate opens"
    ((← r.stopped.get) && (← IO.hasFinished r.listening))

end AppRunnerFailure

unsafe def main (args : List String) : IO Unit := do
  try
    let t ← Checks.new
    let dir := args.headD "out/app-runner-failure/runtime"
    let mode := (args[1]?.getD "all")
    unless ["all", "flush", "network", "suspend"].contains mode do
      throw (IO.userError "unknown AppRunnerFailure mode")
    if mode == "all" || mode == "flush" then AppRunnerFailure.run (dir ++ "/flush") t 0
    if mode == "all" || mode == "network" then AppRunnerFailure.run (dir ++ "/network") t 1
    if mode == "all" || mode == "suspend" then AppRunnerFailure.run (dir ++ "/suspend") t 2
    let result ← t.finish "app-runner-failure"
    (← IO.getStdout).flush
    IO.Process.exit result.toUInt8
  catch e =>
    IO.eprintln s!"unexpected app runner fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
