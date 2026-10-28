/-
The refinement the proofs rest on, tested: random workloads (valid,
forged, malformed and dangling ops) under random schedules (arrival
order, batching, judging interleaved with arrival) run on SQLite and on
the model, and every table must match row for row. At rest the
verdicts must equal the spec's, and different schedules of the same ops
must reach the same verdicts.
-/
import Tests.Lib

open Engine Community Tests

def C := ed25519

inductive Act where
  | ingest (o : Op)
  | step
  | commit

/-- Arrivals in a shuffled order, with judging steps and commits
scattered between them, then judging to rest. -/
def schedule (g : Rng) (ops : List Op) : List Act × Rng := Id.run do
  let (order, g) := g.shuffle ops
  let mut g := g
  let mut acts : Array Act := #[]
  for o in order do
    acts := acts.push (.ingest o)
    let (k, g1) := g.below 4
    let (cm, g2) := g1.below 5
    g := g2
    for _ in [0:k] do acts := acts.push .step
    if cm == 0 then acts := acts.push .commit
  for _ in [0:20 * ops.length + 20] do acts := acts.push .step
  acts := acts.push .commit
  return (acts.toList, g)

def runModel (fam : Family Fact) (acts : List Act) : DB Fact :=
  acts.foldl (fun s a => match a with
    | .ingest o => ingestS o s
    | .step => stepS fam s
    | .commit => s) DB.empty

def runSql (fam : Family Fact) (db : Db) (acts : List Act) : IO Unit := do
  db.exec "BEGIN IMMEDIATE"
  for a in acts do
    match a with
    | .ingest o => (ingest (m := SqlM Fact) o).run db
    | .step => let _ ← (step (m := SqlM Fact) fam).run db
    | .commit => db.exec "COMMIT"; db.exec "BEGIN IMMEDIATE"
  db.exec "COMMIT"

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/differential"
  let seeds := (args.drop 1).head?.bind String.toNat? |>.getD 12
  IO.FS.createDirAll dir
  let t ← Checks.new
  let fam := family C
  let mut counts := (0, 0, 0)
  -- Valid requests, approvals and admissions, so the workload is known
  -- to reach the admission path and not only its refusals.
  let mut admitted := (0, 0, 0)
  for seed in [0:seeds] do
    let ops := workload seed 120
    let ids0 := (ops.map (·.id) ++ ops.flatMap (·.reqs)).eraseDups
    let mut g := Rng.mk (1000 + seed).toUInt64
    let mut verdicts : List (List (Option (Verdict Fact))) := []
    for run in [0:3] do
      let (acts, g') := schedule g ops
      g := g'
      let path := s!"{dir}/s{seed}-{run}.db"
      for suffix in ["", "-wal", "-shm"] do
        if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
      let db ← Db.openAt path
      -- Halfway, then at rest.
      let half := acts.take (acts.length / 3)
      runSql fam db half
      sameTables t s!"seed {seed} run {run} midway" db (runModel fam half) ids0
      -- The writer's budget, read from SQLite, is the proven one; and on
      -- the model it empties the queue.
      let got := half.filterMap fun | .ingest o => some o | _ => none
      let mid := runModel fam half
      db.exec "BEGIN"
      let b ← (budgetSql (F := Fact)).run db
      db.exec "COMMIT"
      t.ok s!"seed {seed} run {run}: SQLite's budget is the proven one" (b == budget got.reverse mid)
      t.ok s!"seed {seed} run {run}: draining with it empties the queue" (drainS fam b mid).queue.isEmpty
      runSql fam db (acts.drop (acts.length / 3))
      let m := runModel fam acts
      sameTables t s!"seed {seed} run {run} at rest" db m ids0
      t.ok s!"seed {seed} run {run}: queue empty at rest" m.queue.isEmpty
      t.ok s!"seed {seed} run {run}: verdicts equal the spec's"
        (ids0.all fun x => m.status x == specOf fam m.ops ops.length x)
      verdicts := verdicts ++ [ids0.map m.status]
      if run == 0 then
        let valid (k : UInt8) := (ops.filter fun o => o.kind == k &&
          match m.status o.id with | some (.valid _) => true | _ => false).length
        admitted := (admitted.1 + valid 12, admitted.2.1 + valid 10, admitted.2.2 + valid 11)
        let vs := ids0.eraseDups.map m.status
        counts := (counts.1 + (vs.filter fun v => match v with | some (.valid _) => true | _ => false).length,
          counts.2.1 + (vs.filter fun v => match v with | some .invalid => true | _ => false).length,
          counts.2.2 + (vs.filter Option.isNone).length)
    t.ok s!"seed {seed}: three schedules, same verdicts" (verdicts.all (· == verdicts.head!))
  IO.println s!"verdicts across seeds: {counts.1} valid, {counts.2.1} invalid, {counts.2.2} unresolved"
  IO.println s!"valid: {admitted.1} requests, {admitted.2.1} approvals, {admitted.2.2} admissions"
  t.ok "the workload admits through approvals" (admitted.1 > 0 && admitted.2.1 > 0 && admitted.2.2 > 0)
  t.finish "differential"
