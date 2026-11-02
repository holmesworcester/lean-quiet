/- Real network boot survives a throwing log and a later App frame error.
The oracle checks the original TCP port, actual Runner/store service and
its final listener release, not only a task-creation counter. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open App Engine Engine.Sync Data Tests Std Std.Async Std.Net
namespace AppNetworkOwnership

def addr (port : UInt16) : SocketAddress := .v4 ⟨IPv4Addr.ofParts 127 0 0 1, port⟩

def freePort : IO UInt16 := do
  let srv ← TCP.Socket.Server.mk
  try
    srv.bind (addr 0)
    srv.listen 1
    match ← srv.getSockName with
    | .v4 a => return a.port
    | _ => throw (IO.userError "unexpected fixture address family")
  finally closeListener srv.native

def available (port : UInt16) : IO Bool := do
  let srv ← TCP.Socket.Server.mk
  let result ← (do
    srv.bind (addr port)
    srv.listen 1).toBaseIO
  closeListener srv.native
  return result.isOk

def step (s : App.St) : IO App.St := return (← (App.step []).run s).2

def run (dir : String) (checks : Checks) (frameFailure : Bool) (adopting : Bool := false) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let armed ← IO.mkRef false
  let starts ← IO.mkRef (0 : Nat)
  let adoptions ← IO.mkRef (0 : Nat)
  let io := { sm.io with
    log := fun line => do
      if line.startsWith "node: starting" then starts.modify (· + 1)
      if line.startsWith "node: listening" then adoptions.modify (· + 1)
      let target := if adopting then "node: listening" else "node: starting"
      if line.startsWith target && !frameFailure then
        if ← armed.modifyGet fun value => (value, false) then
          throw (IO.userError "expected ownership log failure")
      sm.io.log line
    scroll := fun height view => do
      if frameFailure then
        if (← (if adopting then adoptions else starts).get) > 0 then
          if ← armed.modifyGet fun value => (value, false) then
            throw (IO.userError "expected ownership frame failure")
      sm.io.scroll height view }
  let initial ← App.start io (← sm.viewport.get) path
  let initial ← step initial
  let initial ← step initial
  let port ← freePort
  checks.ok "fixture starts from an actually available TCP port" (← available port)
  let mut original := { initial with netCfg := some (port.toNat, true) }
  if adopting then
    original := (← App.netStep.run original).2
    let some task := original.netBoot | throw (IO.userError "actual boot did not retain its task")
    unless ← PublicationFixture.waitFor 2000 (IO.hasFinished task) do
      throw (IO.userError "actual boot did not finish before adoption fault")
  armed.modify (fun _ => true)
  let action : App.M Unit := if frameFailure then discard <| App.step [] else App.netStep
  let result ← (action.run original).toBaseIO
  let expected := if frameFailure then "expected ownership frame failure" else "expected ownership log failure"
  match result with
  | .error error => IO.println s!"observed App failure: {error}"
  | .ok _ => IO.println "observed App result: succeeded (invalid failure precondition)"
  checks.ok "actual App failure occurs after the network boot task was created"
    (match result with | .error e => e.toString.endsWith expected | .ok _ => false)
  checks.ok "rolled-back frame fields retain exactly their pre-action ownership view"
    (original.netBoot.isSome == adopting && original.net.isNone)
  let occupied ← PublicationFixture.waitFor 2000 (return !(← available port))
  checks.ok "the original asynchronous Runner really holds its TCP listener after rollback" occupied
  let owned ← original.netOwner.snapshot
  let retained := owned.boot.isSome || owned.runner.isSome
  checks.ok "shared ownership retains the original boot or live Runner after rollback" retained
  unless retained do return
  let mut state := original
  let end_ := (← IO.monoMsNow) + 3000
  repeat
    state := (← App.netStep.run state).2
    if state.net.isSome || state.netCfg.isNone || (← IO.monoMsNow) ≥ end_ then break
    IO.sleep 1
  checks.ok "a later network stage recovers the original live Runner"
    (state.net.any fun r => r.port == port)
  checks.ok "re-entry does not create a second boot for the already owned listener"
    ((← starts.get) == 1)
  let op := PublicationFixture.root "actual recovered network runner ownership"
  let served ← match state.net with
    | some r => do
      r.write [op]
      PublicationFixture.waitFor 2000 (PublicationFixture.valid state.rd op)
    | none => pure false
  checks.ok "the recovered original Runner actually commits a signed operation" served
  state := (← (App.suspend 250).run state).2
  if let some task := state.netStop then discard <| IO.wait task
  if let some task := state.netReplay then discard <| IO.wait task
  checks.ok "normal App shutdown releases the originally leaked native listener"
    (← available port)

/-- Pointer equality observes retained actual task handles only; it is not
used to establish functional results or manufacture a production outcome. -/
unsafe def sameTask {α : Type} (a b : Option (Task α)) : Bool :=
  match a, b with | some x, some y => ptrEq x y | _, _ => false

unsafe def stopRollback (dir : String) (checks : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let armed ← IO.mkRef false
  let io := { sm.io with ime := fun visible => do
    if !visible then
      if ← armed.modifyGet fun value => (value, false) then
        throw (IO.userError "expected ownership unmount failure")
    sm.io.ime visible }
  let initial ← App.start io (← sm.viewport.get) path
  let initial ← step initial
  let initial ← step initial
  let port ← freePort
  let mut state := { initial with netCfg := some (port.toNat, true) }
  let end_ := (← IO.monoMsNow) + 2000
  repeat
    state := (← App.netStep.run state).2
    if state.net.isSome || (← IO.monoMsNow) ≥ end_ then break
    IO.sleep 1
  let some runner := state.net | throw (IO.userError "stop fixture did not start its actual Runner")
  let closingHeld ← IO.Promise.new
  let release ← IO.Promise.new
  let blocker ← IO.asTask (prio := .dedicated) do
    runner.closing.atomically do
      closingHeld.resolve ()
      discard <| IO.wait release.result?
  discard <| IO.wait closingHeld.result?
  try
    let earlier := PublicationFixture.root "journaled before rollback during normal network stop"
    state := (← (App.submit ⟨[earlier], true⟩).run state).2
    let committed ← PublicationFixture.waitFor 2000 (PublicationFixture.valid state.rd earlier)
    checks.ok "normal stop captures a nonempty real signed-write journal"
      (committed && state.queuedWrites.contains earlier.bytes)
    armed.modify (fun _ => true)
    let failed ← ((App.suspend 150).run state).toBaseIO
    checks.ok "unmount callback really throws after normal stop/replay creation"
      (match failed with | .error e => e.toString.endsWith "expected ownership unmount failure" | _ => false)
    let first ← state.netOwner.snapshot
    checks.ok "shared replay owns the accepted journal bytes after callback rollback"
      (first.journal.contains earlier.bytes)
    let tasksPresent := first.stopping.isSome && first.replay.isSome
    checks.ok "shared owner retains both actual stop/replay tasks despite frame rollback" tasksPresent
    checks.ok "shared owner retains the same original Runner until native cleanup"
      (first.retiredRunner.any (fun old => ptrEq old.done runner.done) && first.runner.isNone)
    unless tasksPresent do return
    checks.ok "native teardown and replay remain unfinished while the real closing mutex is held"
      (!(← first.stopping.mapM (fun task => liftM (IO.hasFinished task))).getD true &&
        !(← first.replay.mapM (fun task => liftM (IO.hasFinished task))).getD true)
    let op := PublicationFixture.root "accepted after rollback during normal network stop"
    state := (← (App.submit ⟨[op], true⟩).run state).2
    checks.ok "direct submit refreshes ownership before touching a stale original Runner"
      (state.net.isNone && state.toNode.toList.flatten.map Op.id == [op.id] &&
        !(← PublicationFixture.valid state.rd op))
    state := (← (App.suspend 10).run state).2
    let second ← state.netOwner.snapshot
    checks.ok "repeated suspend keeps exactly the original stop task" (sameTask first.stopping second.stopping)
    checks.ok "repeated suspend keeps exactly the original replay task" (sameTask first.replay second.replay)
    release.resolve ()
    discard <| IO.wait blocker
    if let some task := first.stopping then discard <| IO.wait task
    if let some task := first.replay then discard <| IO.wait task
    state := (← App.pollRetired.run state).2
    let retired ← state.netOwner.snapshot
    checks.ok "successful cleanup reclaims both fixed original-cap slots"
      (retired.retiredRunner.isNone && retired.retiredBoot.isNone &&
        retired.stopping.isNone && retired.replay.isNone)
    checks.ok "rollback recovery actually closes the original native listener"
      ((← runner.stopped.get) && (← IO.hasFinished runner.listening) && (← available port))
    state := (← (App.onEvent .foreground).run state).2
    let end_ := (← IO.monoMsNow) + 3000
    repeat
      state ← step state
      if ((← PublicationFixture.valid state.rd op) && state.net.isSome) || (← IO.monoMsNow) ≥ end_ then break
      IO.sleep 1
    checks.ok "later parked signed write commits after owned cleanup and genuine restart"
      (← PublicationFixture.valid state.rd op)
    checks.ok "new Runner starts only after the original generation was reclaimed"
      (state.net.any fun next => next.port == port && !ptrEq next.done runner.done)
    let rows ← state.rd.query "SELECT id FROM catalog WHERE id=?" #[op.id]
    checks.ok "later accepted write has exactly one actual catalog row" (rows.size == 1)
    let earlierRows ← state.rd.query "SELECT id FROM catalog WHERE id=?" #[earlier.id]
    checks.ok "replayed earlier signed operation keeps exactly one catalog row" (earlierRows.size == 1)
    state := (← (App.suspend 250).run state).2
    if let some task := state.netStop then discard <| IO.wait task
    if let some task := state.netReplay then discard <| IO.wait task
    checks.ok "the restarted Runner also releases its actual listener" (← available port)
  finally
    release.resolve ()
    discard <| IO.wait blocker
    let owned ← initial.netOwner.snapshot
    stopNodes owned.boot owned.runner
    stopNodes owned.retiredBoot owned.retiredRunner
    runner.stop

end AppNetworkOwnership

unsafe def main (args : List String) : IO Unit := do
  try
    let checks ← Checks.new
    let dir := args.headD "out/app-network-ownership/runtime"
    let mode := args[1]?.getD "all"
    unless ["all", "log", "frame", "adopt-log", "adopt-frame", "stop"].contains mode do
      throw (IO.userError "unknown network ownership fixture mode")
    if mode == "all" || mode == "log" then AppNetworkOwnership.run (dir ++ "/log") checks false
    if mode == "all" || mode == "frame" then AppNetworkOwnership.run (dir ++ "/frame") checks true
    if mode == "all" || mode == "adopt-log" then AppNetworkOwnership.run (dir ++ "/adopt-log") checks false true
    if mode == "all" || mode == "adopt-frame" then AppNetworkOwnership.run (dir ++ "/adopt-frame") checks true true
    if mode == "all" || mode == "stop" then AppNetworkOwnership.stopRollback (dir ++ "/stop") checks
    let result ← checks.finish "app-network-ownership"
    (← IO.getStdout).flush
    IO.Process.exit result.toUInt8
  catch e =>
    IO.eprintln s!"unexpected app ownership fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
