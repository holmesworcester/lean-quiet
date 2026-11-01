/- Actual channel-admitted writes survive a normal App suspend even when
its Runner fails after the entry observation, or clean shutdown leaves work
in the local lane. Hooks pause real handlers after a signed SQLite commit. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open App Engine Engine.Sync Data Tests
namespace AppSuspendJournal

def waitFor := PublicationFixture.waitFor

def stored (db : Db) (op : Op) : IO Bool := PublicationFixture.valid db op

def step (state : App.St) : IO App.St := do
  return (← (App.step []).run state).2

def journal (db : Db) : IO (List ByteArray) := do
  let cp ← Lifecycle.load db
  return (cp.bind fun cp =>
    (Codec.decode (cp.2.2.2.2.2[10]?.getD .empty) : Option (List ByteArray))).getD []

def run (dir : String) (t : Checks) (fail : Bool) (holdStop : Bool := false) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let initial ← App.start sm.io (← sm.viewport.get) path
  let initial ← step initial
  let initial ← step initial
  let first := PublicationFixture.root "committed before normal suspend"
  let waiting := (List.range 5).map fun i =>
    PublicationFixture.root s!"admitted before normal suspend {i}"
  let later := PublicationFixture.root "accepted while normal stop still owns runner"
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let armed ← IO.mkRef true
  let hooks := Connection.hooks fam Connection.sodium .empty
  let x : Sync SF (SqlM SF) := { fam, hooks := { hooks with react := do
    let ready ← (Store.getStatus first.id : SqlM SF _)
    if ready.isSome && (← armed.modifyGet fun value => (value, false)) then
      entered.resolve ()
      discard <| IO.wait release.result?
      if fail then throw (IO.userError "expected normal-suspend post-commit hook failure")
    hooks.react } }
  let r ← Runner.start x (← openDb path) 0 0 (cfg := { queue := 8 })
  let stoppingHeld ← IO.Promise.new
  let releaseStop ← IO.Promise.new
  let stopOwner ← IO.asTask (prio := .dedicated) do
    if holdStop then
      r.closing.atomically do
        stoppingHeld.resolve ()
        discard <| IO.wait releaseStop.result?
    else stoppingHeld.resolve ()
  discard <| IO.wait stoppingHeld.result?
  let mut state := { initial with net := some r, netCfg := some (0, true) }
  try
    state := (← (App.submit ⟨[first], true⟩).run state).2
    unless ← waitFor 2000 entered.isResolved do
      throw (IO.userError "actual first signed write never reached its post-commit gate")
    t.ok "first signed operation is committed before the real handler is paused"
      (← stored state.rd first)
    for op in waiting do state := (← (App.submit ⟨[op], true⟩).run state).2
    let saved ← waitFor 2000 state.wr.saveDone
    let durable ← journal state.rd
    t.ok "accepted local channel writes leave parked queue but retain durable journal bytes"
      (saved && state.toNode.isEmpty && waiting.all (fun op => durable.contains op.bytes))
    t.ok "normal suspend entry observes a genuinely unfinished Runner"
      (!(← IO.hasFinished r.done) && state.net.isSome)
    state := (← (App.suspend 150).run state).2
    state := { state with active := false }
    t.ok "bounded suspend retains unfinished stop task without retaining mounted runner"
      (state.net.isNone && state.netStop.isSome && !(← IO.hasFinished r.done))
    t.ok "actual stop request respects the held App-owned stop call owner"
      ((← r.stopped.get) == !holdStop)
    t.ok "replay does not overtake the original runner's unfinished SQLite handler"
      (!(← waiting.anyM (stored state.rd)))
    state := (← (App.submit ⟨[later], true⟩).run state).2
    t.ok "a later accepted write parks behind the retained stop task"
      (state.toNode.toList.flatten.map Op.id == [later.id])
    let durableSaved ← waitFor 2000 state.wr.saveDone
    t.ok "checkpoint retains both pre-stop and later accepted bytes"
      (durableSaved && (← journal state.rd).contains later.bytes &&
        waiting.all (fun op => state.queuedWrites.contains op.bytes))
    release.resolve ()
    unless ← waitFor 3000 (IO.hasFinished r.done) do
      throw (IO.userError "released actual runner did not finish stopping")
    t.ok "actual runner completion matches the controlled clean or failing shutdown"
      (r.done.get.isOk == !fail)
    if holdStop then
      let recovered ← waitFor 3000 (waiting.allM (stored state.rd))
      t.ok "journal replay uses loop completion without waiting for held App-owned stop call" recovered
      t.ok "unfinished App-owned stop call and its actual mutex owner stay retained"
        (state.netStop.isSome && !(← IO.hasFinished stopOwner))
      t.ok "later accepted write remains parked while normal native stop is unfinished"
        (!(← stored state.rd later) && state.toNode.toList.flatten.map Op.id == [later.id])
    releaseStop.resolve ()
    discard <| IO.wait stopOwner
    if let some task := state.netStop then
      unless ← waitFor 3000 (IO.hasFinished task) do
        throw (IO.userError "actual retained stop task did not finish")
    state := (← App.pollRetired.run state).2
    state := (← (App.onEvent .foreground).run state).2
    let start ← IO.monoMsNow
    repeat
      state ← step state
      let all ← waiting.allM (stored state.rd)
      if (all && (← stored state.rd later)) || (← IO.monoMsNow) ≥ start + 3000 then break
      IO.sleep 1
    let all ← waiting.allM (stored state.rd)
    t.ok "all previously channel-admitted signed writes commit after normal resume" all
    t.ok "the later accepted signed write also commits through normal foreground stages"
      (← stored state.rd later)
    let rows ← state.rd.query "SELECT id FROM catalog ORDER BY seq" #[]
    let ids := rows.toList.filterMap (·[0]?)
    let expected := (first :: waiting ++ [later]).map Op.id
    t.ok "actual catalog preserves accepted order across stop replay and later writes"
      (ids.filter expected.contains == expected)
    t.ok "replayed already committed operations retain exactly one catalog entry"
      (expected.all fun id => (ids.filter (· == id)).length == 1)
    state ← step state
    t.ok "App journal retires recovered bytes only after actual store observation"
      (state.queuedWrites.isEmpty)
    t.ok "normal stop completion permits actual foreground frame publication"
      ((← sm.frames.get) > 2 && state.netStop.isNone && state.life.mounted)
    state := (← (App.suspend 250).run state).2
    if let some task := state.netStop then
      discard <| IO.wait task
  finally
    release.resolve ()
    releaseStop.resolve ()
    discard <| IO.wait stopOwner
    r.stop
  t.ok "the original listener is stopped after normal suspend"
    ((← r.stopped.get) && (← IO.hasFinished r.listening))

end AppSuspendJournal

def main (args : List String) : IO Unit := do
  try
    let t ← Checks.new
    let dir := args.headD "out/app-suspend-journal/runtime"
    let mode := args[1]?.getD "all"
    unless ["all", "failure", "clean", "held-stop"].contains mode do
      throw (IO.userError "invalid normal suspend test mode")
    if mode == "all" || mode == "failure" then AppSuspendJournal.run (dir ++ "/failure") t true
    if mode == "all" || mode == "clean" then AppSuspendJournal.run (dir ++ "/clean") t false
    if mode == "all" || mode == "held-stop" then AppSuspendJournal.run (dir ++ "/held-stop") t true true
    let result ← t.finish "app-suspend-journal"
    (← IO.getStdout).flush
    IO.Process.exit result.toUInt8
  catch e =>
    IO.eprintln s!"unexpected app suspend fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
