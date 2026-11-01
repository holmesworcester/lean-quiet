/- Exercise the diagnostic recorder through actual non-chat and chat frames.
The old non-chat branch accumulated every sample forever. -/
import platforms.headless.Sim
import tests.engine.Checks

open App Tests
namespace AppFrameTimes

def exercise (sm : Sim) (checks : Checks) (state : App.St) (label : String) : IO App.St := do
  let mut state := { state with times := #[] }
  let initialFrames ← sm.frames.get
  let mut bounded := true
  let mut latest := true
  let begin ← IO.monoMsNow
  for _ in [:650] do
    let before := state.times
    state := (← (App.step []).run state).2
    bounded := bounded && state.times.size ≤ 600
    let retained := if before.size ≥ 600 then before.extract 300 before.size else before
    latest := latest && state.times.pop == retained
  IO.println s!"native {label}650 frame observation: {(← IO.monoMsNow) - begin}ms (not a universal bound)"
  checks.ok s!"{label}: actual App publishes all650 consecutive frames"
    ((← sm.frames.get) == initialFrames + 650)
  checks.ok s!"{label}: every completed frame retains at most600 timing samples" bounded
  checks.ok s!"{label}: recorder preserves the existing600/300 policy and sample order" latest
  checks.ok s!"{label}: actual recorder reaches the expected post-trim350 samples"
    (state.times.size == 350)
  return state

def run (dir : String) (checks : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  sm.viewport.set #[320, 600, 16, 12, 160]
  let initial ← App.start sm.io (← sm.viewport.get) path
  let state ← exercise sm checks initial "non-chat"
  let (_, state) ← (show App.M Unit from do
    App.found "Frame samples" "Alice"
    waitIdle sm
    App.openPage .chat
    discard <| App.sendText "real signed message during diagnostic sampling"
    waitIdle sm).run state
  checks.ok "chat sampling has a real signed conversation row"
    (state.total == 1 && !state.rows.isEmpty)
  let state ← exercise sm checks state "chat"
  discard <| (App.suspend 100).run state

end AppFrameTimes

def main (args : List String) : IO Unit := do
  try
    let checks ← Checks.new
    AppFrameTimes.run (args.headD "out/app-frame-times/runtime") checks
    let result ← checks.finish "app-frame-times"
    (← IO.getStdout).flush
    IO.Process.exit result.toUInt8
  catch e =>
    IO.eprintln s!"unexpected frame times fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
