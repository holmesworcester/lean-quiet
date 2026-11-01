/- Returning OS diagnostic errors must not drop selected or retried writes.
The runner redirects real stderr to Linux /dev/full. All assertions and
unexpected-error output use stdout so diagnostic failure cannot hide them. -/
import tests.engine.PublicationFixture
import tests.engine.Checks

open Engine Data Tests PublicationFixture

namespace WriterDiagnostics

def checkpoint (n : Nat) : Lifecycle.Checkpoint :=
  (1, n, "diagnostic-owner".toUTF8, "diagnostic-message".toUTF8, n, [])

def hideCheckpoint (db : Db) : IO Unit :=
  db.exec "ALTER TABLE app_ops RENAME TO checkpoint_unavailable"

def restoreCheckpoint (db : Db) : IO Unit :=
  db.exec "ALTER TABLE checkpoint_unavailable RENAME TO app_ops"

def check (t : Checks) (name : String) (value : Bool) : IO Unit := do
  if value then t.passed.modify (· + 1)
  else
    t.failed.modify (· + 1)
    IO.println s!"FAIL: {name}"

def checkpointError (t : Checks) (dir : String) : IO Unit := do
  let (path, db) ← database (dir ++ "/checkpoint")
  let observer ← Db.openAt path
  let w ← writer
  let op := root "signed write despite failed checkpoint diagnostic"
  w.submit ⟨[op], true⟩
  w.save (Codec.encode (checkpoint 7))
  hideCheckpoint db
  let attempt ← (w.turn db Lifecycle.save).toBaseIO
  let readable ← valid observer op
  IO.println s!"checkpoint diagnostic: returned={attempt.isOk}, readable={readable}, busy={← w.busy.get}, commits={← w.count.get}"
  check t "checkpoint diagnostic error cannot escape the selected writer turn" attempt.isOk
  check t "selected signed write commits while checkpoint table and stderr fail" readable
  check t "diagnostic failure cannot lose the selected job's busy ownership"
    ((← w.busy.get) == 0 && (← w.count.get) == 1 && (← w.jobs.get).isEmpty)
  check t "failed checkpoint remains owned despite its failed diagnostic"
    ((← w.saving.get) == (1, some (Codec.encode (checkpoint 7))) &&
      (← w.saved.get) == 0 && !(← w.saveDone))
  restoreCheckpoint db
  discard <| w.turn db Lifecycle.save
  check t "later real checkpoint recovery preserves the committed signed write"
    ((← w.saveDone) && (← Lifecycle.load observer) == some (checkpoint 7) &&
      (← valid observer op))
  let rows ← observer.query "SELECT id FROM catalog ORDER BY seq" #[]
  check t "diagnostic recovery has exactly one actual catalog entry"
    (rows.toList.filterMap (·[0]?) == [op.id])

def jobError (t : Checks) (dir : String) : IO Unit := do
  let (_, db) ← database (dir ++ "/job")
  let w ← writer
  let op := root "retry signed write despite failed job diagnostic"
  db.exec "CREATE TRIGGER refuse_diagnostic_job BEFORE INSERT ON ops BEGIN SELECT RAISE(ABORT, 'expected diagnostic job failure'); END"
  w.submit ⟨[op], true⟩
  let attempt ← (w.turn db Lifecycle.save).toBaseIO
  check t "job diagnostic error cannot stop the writer after retaining its retry" attempt.isOk
  let queue ← w.jobs.get
  check t "failed job retains one real retry even when its diagnostic fails"
    (queue.writes.flatMap (fun j => j.ops.map (·.id)) == [op.id] && queue.events.isEmpty &&
      (← w.busy.get) == 1 && (← w.count.get) == 0 && !(← valid db op))
  db.exec "DROP TRIGGER refuse_diagnostic_job"
  discard <| w.turn db Lifecycle.save
  check t "retained retry commits after the actual SQL fault is removed"
    ((← valid db op) && (← w.busy.get) == 0 && (← w.count.get) == 1 &&
      (← w.jobs.get).isEmpty)
  let rows ← db.query "SELECT id FROM catalog ORDER BY seq" #[]
  check t "retry after failed diagnostic cannot duplicate the catalog entry"
    (rows.toList.filterMap (·[0]?) == [op.id])

end WriterDiagnostics

def main (args : List String) : IO Unit := do
  try
    let t ← Checks.new
    let probe ← (IO.eprintln "real stderr failure probe").toBaseIO
    WriterDiagnostics.check t "real stderr returns an OS write error" (!probe.isOk)
    let dir := args.headD "out/writer-job-retry/diagnostics"
    WriterDiagnostics.checkpointError t dir
    WriterDiagnostics.jobError t dir
    let code ← t.finish "writer-diagnostics"
    (← IO.getStdout).flush
    IO.Process.exit code.toUInt8
  catch error =>
    IO.println s!"unexpected writer diagnostics fixture error: {error}"
    (← IO.getStdout).flush
    IO.Process.exit 2
