/- The actual writer loop polls a paused writer while the UI publishes resume.
Real signed roots must become valid SQLite rows after the forced overlap. -/
import tests.engine.PublicationFixture
open Engine Data PublicationFixture

def run (args : List String) : IO UInt32 := do
  let (path, db) ← database (args.headD "out/ref-publications/resume")
  let reading ← Db.openAt path
  let w ← writer true
  let op := root "resumed writer root"
  w.submit ⟨[op], true⟩
  armBool w.paused
  let resume ← IO.asTask (prio := .dedicated) do
    waitRelease
    entered
    w.setPaused false
    done
  let _ ← IO.asTask (prio := .dedicated) (w.loop db Lifecycle.save)
  let result ← IO.wait resume
  let applied ← waitFor 1000 do return (← valid reading op) && (← w.busy.get) == 0
  let paused ← w.paused.get
  if !(← injected) || !result.isOk || paused || !applied || (← w.busy.get) != 0 then
    IO.eprintln s!"FAIL: actual writer resumes and commits its queued valid op after the overlapping pause read (paused={paused}, applied={applied}, busy={← w.busy.get})"
    return 1
  -- Deliberate pause retains its original behavior; the atomic publication
  -- must not turn the pause/resume controls into unconditional unpausing.
  w.setPaused true
  IO.sleep 20
  let next := root "second paused writer root"
  w.submit ⟨[next], true⟩
  IO.sleep 30
  unless !(← valid reading next) && (← w.busy.get) == 1 do
    IO.eprintln "FAIL: deliberate writer pause retains the later queued job"
    return 1
  w.setPaused false
  unless ← waitFor 1000 (valid reading next) do
    IO.eprintln "FAIL: later explicit resume releases the deliberately paused job"
    return 1
  IO.println "writer-resume: actual writer commits valid queued ops after SDK overlap; deliberate pause remains effective"
  return 0

-- The production writer intentionally runs forever; the fixture owns process
-- lifetime instead of waiting for that dedicated task during runtime teardown.
def main (args : List String) : IO Unit := do
  let code ← run args
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
