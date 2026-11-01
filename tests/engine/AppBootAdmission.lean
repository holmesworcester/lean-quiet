/- Boot acquires a retained task before waiting for earlier Writer work.
Later actual App submissions park; they cannot prolong that finite drain.
This fixture uses the real Writer.loop, Runner and signed SQLite commits. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open App Engine Engine.Sync Data Tests
namespace AppBootAdmission

def step (s : App.St) : IO App.St := do
  return (← (App.step []).run s).2

def stored (s : App.St) (op : Op) : IO Bool := PublicationFixture.valid s.rd op

def run (dir : String) (checks : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let initial ← App.start sm.io (← sm.viewport.get) path
  let initial ← step initial
  let initial ← step initial
  let first := PublicationFixture.root "actual writer accepted before network boot"
  let later := (List.range 12).map fun i =>
    PublicationFixture.root s!"continuing App submission while boot awaits old writer {i}"
  initial.wr.setPaused true
  let mut state := initial
  try
    state := (← (App.submit ⟨[first], true⟩).run state).2
    state := { state with netCfg := some (0, true) }
    checks.ok "earlier signed write is retained in the paused actual Writer"
      ((← state.wr.busy.get) == 1 && !(← stored state first))
    let before ← sm.frames.get
    state := (← App.netStep.run state).2
    checks.ok "first network service installs an owned boot task before earlier work finishes"
      (state.netBoot.isSome && state.net.isNone)
    -- Give an incorrectly eager task time to actually open/start. The fixed
    -- task remains held by the real Writer, not by a substitute boot gate.
    if let some task := state.netBoot then
      discard <| PublicationFixture.waitFor 500 (IO.hasFinished task)
    for op in later do
      state := (← (App.submit ⟨[op], true⟩).run state).2
      state ← step state
    checks.ok "continuing App submissions park in accepted order behind boot"
      (state.toNode.toList.flatten.map Op.id == later.map Op.id)
    checks.ok "later App writes cannot extend the pre-boot Writer backlog"
      ((← state.wr.busy.get) == 1)
    checks.ok "actual foreground frames complete while pre-boot storage service is paused"
      ((← sm.frames.get) ≥ before + later.length)
    checks.ok "retained boot does not install a runner ahead of earlier Writer commits"
      (state.netBoot.isSome && state.net.isNone &&
        !(← state.netBoot.mapM (fun task => liftM (IO.hasFinished task))).getD true)
    -- Completed App frames do not imply service by its separate Runner.
    -- In an incorrectly early boot, observe a completed real write turn
    -- before inspecting whether it overtook the still-paused Writer.
    if let some runner := state.net then
      unless ← PublicationFixture.waitFor 2000 (do return (← runner.counters).writes > 0) do
        throw (IO.userError "premature runner did not complete its actual write service")
    checks.ok "no later signed operation overtakes the paused pre-boot write"
      (!(← later.anyM (stored state)))
    let saved ← PublicationFixture.waitFor 2000 state.wr.saveDone
    let cp ← Lifecycle.load state.rd
    let durable := cp.bind fun cp =>
      (Codec.decode (cp.2.2.2.2.2[10]?.getD .empty) : Option (List ByteArray))
    checks.ok "checkpoint owns every parked and pre-boot accepted byte"
      (saved && (first :: later).all (fun op => (durable.getD []).contains op.bytes))
    state.wr.setPaused false
    let end_ := (← IO.monoMsNow) + 3000
    repeat
      state ← step state
      let ready ← (first :: later).allM (stored state)
      if (ready && state.net.isSome && state.toNode.isEmpty) || (← IO.monoMsNow) ≥ end_ then break
      IO.sleep 1
    checks.ok "actual boot and all parked writes progress after finite earlier service"
      (state.net.isSome && state.netBoot.isNone && state.toNode.isEmpty &&
        (← (first :: later).allM (stored state)))
    let rows ← state.rd.query "SELECT id FROM catalog ORDER BY seq" #[]
    let ids := rows.toList.filterMap (·[0]?)
    let expected := (first :: later).map Op.id
    checks.ok "real SQLite catalog orders the pre-boot write before all later submissions"
      (ids.filter expected.contains == expected)
    checks.ok "each accepted signed op has exactly one catalog entry"
      (expected.all fun id => (ids.filter (· == id)).length == 1)
    state ← step state
    checks.ok "actual App store observation retires the now-committed journal"
      state.queuedWrites.isEmpty
    state := (← (App.suspend 250).run state).2
    if let some task := state.netStop then discard <| IO.wait task
    if let some task := state.netReplay then discard <| IO.wait task
    checks.ok "the started runner's normal stop and replay tasks finish"
      ((← state.netStop.mapM (fun task => liftM (IO.hasFinished task))).getD true &&
        (← state.netReplay.mapM (fun task => liftM (IO.hasFinished task))).getD true)
  finally
    initial.wr.setPaused false

end AppBootAdmission

def main (args : List String) : IO Unit := do
  try
    let checks ← Checks.new
    AppBootAdmission.run (args.headD "out/app-boot-admission/runtime") checks
    let result ← checks.finish "app-boot-admission"
    (← IO.getStdout).flush
    IO.Process.exit result.toUInt8
  catch e =>
    IO.eprintln s!"unexpected app boot fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
