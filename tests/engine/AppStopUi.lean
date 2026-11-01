/- The actual App resumes its display and threaded Reader while ordinary
network shutdown is held at the original Runner's closing mutex. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open App Engine Engine.Sync Data Tests
namespace AppStopUi

def turn (s : App.St) (events : List App.Event := []) : IO App.St :=
  return (← (App.step events).run s).2

unsafe def run (dir : String) (checks : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  sm.viewport.set #[720, 1280, 32, 24, 160]
  let initial ← App.start sm.io (← sm.viewport.get) path
  let (_, initial) ← (show App.M Unit from do
    App.found "Cleanup UI" "Alice"
    waitIdle sm
    App.openPage .chat
    discard <| App.sendText "stored before normal native cleanup"
    waitIdle sm).run initial
  checks.ok "fixture has a real signed conversation row and published pixels"
    (initial.total == 1 && initial.rows.size > 0 && (← sm.frames.get) > 0)
  let x : Sync SF (SqlM SF) := { fam, hooks := Data.hooks .empty }
  let runner ← Runner.start x (← openDb path) 0 0
  let mut state := (← (App.attachNetwork none (some runner)).run initial).2
  let held ← IO.Promise.new
  let release ← IO.Promise.new
  let blocker ← IO.asTask (prio := .dedicated) do
    runner.closing.atomically do
      held.resolve ()
      discard <| IO.wait release.result?
  discard <| IO.wait held.result?
  try
    state := (← (App.suspend 20).run state).2
    state := { state with active := false, threaded := true }
    let owned ← state.netOwner.snapshot
    let some stopping := owned.stopping | throw (IO.userError "missing actual stop task")
    checks.ok "normal cleanup holds the original Runner and unfinished native stop"
      (owned.retiredRunner.any (fun r => ptrEq r.done runner.done) &&
        !(← IO.hasFinished stopping) && !(← IO.hasFinished blocker))
    let frames ← sm.frames.get
    let begin ← IO.monoMsNow
    state ← turn state [.foreground]
    let elapsed := (← IO.monoMsNow) - begin
    IO.println s!"native foreground observation: {elapsed}ms (not a universal latency bound)"
    checks.ok "first completed foreground stage publishes a frame during normal cleanup"
      ((← sm.frames.get) == frames + 1)
    checks.ok "first completed foreground stage mounts the actual conversation"
      (state.life.mounted && state.mountedPage == some (.chat, initial.cur))
    checks.ok "foreground starts the actual threaded Reader while cleanup remains held"
      state.reader.isSome
    let drafts := "typing while ordinary cleanup is held"
    sm.input.set drafts
    state ← turn state [.text]
    checks.ok "the next completed frame accepts typing during normal cleanup"
      (state.text == drafts && state.native == drafts && (← sm.frames.get) == frames + 2)
    let read ← PublicationFixture.waitFor 2000 do
      return !(← state.sh.board.get).vals.isEmpty
    checks.ok "resumed threaded Reader publishes real SQLite answers before native cleanup"
      (read && state.reader.isSome)
    let later := PublicationFixture.root "new signed write parked during native cleanup"
    state := (← (App.submit ⟨[later], true⟩).run state).2
    checks.ok "UI progress preserves the normal stop write-ordering barrier"
      (state.toNode.toList.flatten.any (·.id == later.id) &&
        !(← PublicationFixture.valid state.rd later))
    let current ← state.netOwner.snapshot
    checks.ok "UI progress retains the exact original cleanup generation"
      (current.stopping.any (fun task => ptrEq task stopping) &&
        current.retiredRunner.any (fun r => ptrEq r.done runner.done) &&
        !(← IO.hasFinished stopping) && !(← IO.hasFinished blocker))
    checks.ok "UI progress cannot start a replacement Runner before cleanup"
      (current.boot.isNone && current.runner.isNone)
    release.resolve ()
    discard <| IO.wait blocker
    unless ← PublicationFixture.waitFor 3000 (IO.hasFinished stopping) do
      throw (IO.userError "released native stop did not complete")
    if let some replay := current.replay then
      unless ← PublicationFixture.waitFor 3000 (IO.hasFinished replay) do
        throw (IO.userError "released replay did not complete")
    state := (← App.pollRetired.run state).2
    state := (← App.flushNode.run state).2
    let stored ← PublicationFixture.waitFor 3000 (PublicationFixture.valid state.rd later)
    checks.ok "parked signed operation commits after the actual cleanup barrier clears" stored
    checks.ok "original Runner cleanup still closes its native listener"
      ((← runner.stopped.get) && (← IO.hasFinished runner.listening))
    state := (← (App.suspend 100).run state).2
    if let some worker := state.readerStop then
      discard <| IO.wait worker.done
  finally
    release.resolve ()
    discard <| IO.wait blocker
    if let some worker := state.reader then worker.requestStop
    if let some worker := state.readerStop then worker.requestStop
    runner.stop

end AppStopUi

unsafe def main (args : List String) : IO Unit := do
  try
    let checks ← Checks.new
    AppStopUi.run (args.headD "out/app-stop-ui/runtime") checks
    let result ← checks.finish "app-stop-ui"
    (← IO.getStdout).flush
    IO.Process.exit result.toUInt8
  catch e =>
    IO.eprintln s!"unexpected app stop UI fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
