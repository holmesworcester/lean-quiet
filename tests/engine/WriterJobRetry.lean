/- Selective real SQLite write failure: accepted jobs stay owned, while
healthy queued work in either class still receives its service opportunity. -/
import tests.engine.PublicationFixture
import tests.engine.Checks

open Engine Data Tests PublicationFixture

namespace WriterJobRetry

def ids (jobs : List Job) : List Id := jobs.flatMap (fun j => j.ops.map (·.id))

def run (t : Checks) (dir : String) : IO Unit := do
  let (_, db) ← database dir
  let w ← writer
  let failed := root "temporarily refused signed root"
  let healthy := root "healthy local behind refused root"
  let background := root "healthy background behind refused root"
  db.exec "CREATE TABLE refused_job (id BLOB PRIMARY KEY)"
  discard <| db.query "INSERT INTO refused_job VALUES (?)" #[failed.id]
  db.exec "CREATE TRIGGER refuse_one_job BEFORE INSERT ON ops WHEN EXISTS (SELECT 1 FROM refused_job WHERE id=NEW.id) BEGIN SELECT RAISE(ABORT, 'expected selective write failure'); END"
  w.submit ⟨[failed], true⟩
  w.submit ⟨[healthy], true⟩
  w.submit ⟨[background], false⟩
  let selected ← w.turn db Lifecycle.save
  let queue ← w.jobs.get
  t.ok "a real SQL failure still completes its selected attempt"
    (selected.any (fun j => ids [j] == [failed.id]))
  t.ok "failed job rejoins its own FIFO behind retained work"
    (ids queue.writes == [healthy.id, failed.id] && ids queue.events == [background.id])
  t.ok "failed attempt retains exactly one busy owner without counting a commit"
    ((← w.busy.get) == 3 && (← w.count.get) == 0)
  t.ok "failed signed operation has not escaped its actual SQL transaction"
    ((← (Q.op failed.id).run db #[]) == .bytes none)
  discard <| w.turn db Lifecycle.save
  t.ok "healthy local job proceeds while the original job still fails"
    ((← valid db healthy) && !(← valid db failed))
  discard <| w.turn db Lifecycle.save
  t.ok "repeated failure does not duplicate or discharge its busy owner"
    ((← w.busy.get) == 2 && (← w.count.get) == 1)
  discard <| w.turn db Lifecycle.save
  t.ok "failed retries preserve the reserved background slot"
    ((← valid db background) && (← w.count.get) == 2 && (← w.busy.get) == 1)
  t.ok "only the originally refused job remains queued before recovery"
    (ids (← w.jobs.get).writes == [failed.id] && (← w.jobs.get).events.isEmpty)
  db.exec "DROP TRIGGER refuse_one_job"
  discard <| w.turn db Lifecycle.save
  t.ok "the retained signed job commits after the actual SQL fault is removed"
    ((← valid db failed) && (← valid db healthy) && (← valid db background))
  t.ok "successful recovery discharges every admission exactly once"
    ((← w.busy.get) == 0 && (← w.count.get) == 3 && (← w.jobs.get).isEmpty)
  let rows ← db.query "SELECT id FROM catalog ORDER BY seq" #[]
  t.ok "actual catalog records healthy work before the recovered job without duplicates"
    (rows.toList.filterMap (·[0]?) == [healthy.id, background.id, failed.id])

end WriterJobRetry

def main (args : List String) : IO Unit := do
  let t ← Checks.new
  WriterJobRetry.run t (args.headD "out/writer-job-retry/selected")
  let code ← t.finish "writer-job-retry"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
