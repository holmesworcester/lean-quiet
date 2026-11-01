/- The production Writer.loop, with real signed ops and SQLite. Its actual
checkpoint callback gates each iteration after selection and before the
selected job commits; submissions continue between those completed turns.
No substitute queue or sync transport determines selection. -/
import tests.engine.PublicationFixture
import tests.engine.Checks

open Engine Data Tests PublicationFixture

namespace WriterFairness

/-- Native representation check on actual submit: adding one class must not
rebuild the other class's backlog. This is a runtime check, not a Lean proof
of allocation cost; retaining both snapshots makes sharing observable. -/
unsafe def oppositeLaneSharing (t : Checks) : IO Unit := do
  let w ← writer
  let background := root "retained background backlog"
  let localOp := root "retained local backlog"
  for _ in [:128] do w.submit ⟨[background], false⟩
  let before ← w.jobs.get
  w.submit ⟨[localOp], true⟩
  let after ← w.jobs.get
  t.ok "actual local submission retains the background backlog without rebuilding it"
    (ptrEq before.events after.events && after.events.length == 128)
  for _ in [:127] do w.submit ⟨[localOp], true⟩
  let before ← w.jobs.get
  w.submit ⟨[background], false⟩
  let after ← w.jobs.get
  t.ok "actual background submission retains the local backlog without rebuilding it"
    (ptrEq before.writes after.writes && after.writes.length == 128)

def checkpoint (i : Nat) : ByteArray :=
  Codec.encode ((1, i, ByteArray.empty, ByteArray.empty, 0, []) : Lifecycle.Checkpoint)

def catalog (db : Db) : IO (List Id) := do
  let rows ← db.query "SELECT id FROM catalog ORDER BY seq" #[]
  return rows.toList.filterMap (·[0]?)

def promiseAt (ps : List (IO.Promise Unit)) (i : Nat) : IO (IO.Promise Unit) :=
  match ps[i]? with
  | some p => pure p
  | none => throw (IO.userError "missing writer fixture gate")

def ready (p : IO.Promise Unit) : IO Unit := do
  unless ← waitFor 3000 p.isResolved do
    throw (IO.userError "actual writer did not reach its next checkpoint gate")

def runningLoop (t : Checks) (dir : String) : IO Unit := do
  let (path, db) ← database (dir ++ "/loop")
  let observe ← Db.openAt path
  let w ← writer
  let local0 := root "oldest accepted local"
  let local1 := root "second accepted local"
  let back0 := root "oldest accepted background"
  let back1 := root "second accepted background"
  let localNew := (List.range 16).map fun i => root s!"continuing local {i}"
  let backNew := (List.range 16).map fun i => root s!"continuing background {i}"
  for op in [local0, local1] do w.submit ⟨[op], true⟩
  for op in [back0, back1] do w.submit ⟨[op], false⟩
  let gates ← (List.range 17).mapM fun _ => (IO.Promise.new : IO (IO.Promise Unit))
  let entered ← (List.range 17).mapM fun _ => (IO.Promise.new : IO (IO.Promise Unit))
  w.save (checkpoint 0)
  let _ ← IO.asTask (prio := .dedicated) (w.loop db fun db bytes => do
    Lifecycle.save db bytes
    let some cp := Lifecycle.restore bytes | throw (IO.userError "checkpoint gate payload")
    let i := cp.2.1
    let some signal := entered[i]? | throw (IO.userError "unexpected checkpoint gate")
    let some release := gates[i]? | throw (IO.userError "missing checkpoint release")
    signal.resolve ()
    discard <| IO.wait release.result?)
  for i in [:16] do
    ready (← promiseAt entered i)
    -- Both classes keep accepting work before the next service iteration.
    w.submit ⟨[localNew[i]!], true⟩
    w.submit ⟨[backNew[i]!], false⟩
    w.save (checkpoint (i + 1))
    (← promiseAt gates i).resolve ()
  ready (← promiseAt entered 16)
  -- Sixteen actual jobs have committed. The seventeenth is selected and
  -- held by its real checkpoint callback, so inspection cannot race commit.
  let trace ← catalog observe
  let localIds := ([local0, local1] ++ localNew).map (·.id)
  let backIds := ([back0, back1] ++ backNew).map (·.id)
  t.ok "actual loop commits exactly one real op per gated service turn" (trace.length == 16)
  t.ok "oldest accepted local commits within two turns despite continuing local arrivals"
    ((trace.take 2).contains local0.id)
  t.ok "second accepted local commits within four turns despite continuing local arrivals"
    ((trace.take 4).contains local1.id)
  t.ok "oldest background commits within four turns under continuing local submissions"
    ((trace.take 4).contains back0.id)
  t.ok "second background commits within eight turns under continuing local submissions"
    ((trace.take 8).contains back1.id)
  t.ok "real loop serves three local jobs first and reserves the fourth for background"
    ((trace.take 4).map localIds.contains == [true, true, true, false])
  t.ok "every four busy turns preserve the local three-to-one service share"
    ((List.range 4).all fun block =>
      (((trace.drop (4 * block)).take 4).filter localIds.contains).length == 3)
  t.ok "committed local jobs preserve their actual submission FIFO"
    (trace.filter localIds.contains == localIds.take 12)
  t.ok "committed background jobs preserve their actual submission FIFO"
    (trace.filter backIds.contains == backIds.take 4)
  let mut allValid := true
  for op in [local0, local1, back0, back1] ++ localNew ++ backNew do
    if trace.contains op.id && !(← valid observe op) then allValid := false
  t.ok "every selected signed op is valid in the real SQLite store" allValid
  -- Stop at an iteration boundary; do not change the selected job's meaning.
  w.setPaused true
  (← promiseAt gates 16).resolve ()
  let settled ← waitFor 3000 do return (← w.count.get) == 17 && (← w.busy.get) == 19
  unless settled do
    throw (IO.userError "last writer job did not settle before pause")
  let trace ← catalog observe
  let queued ← w.jobs.get
  let waiting := (queued.writes ++ queued.events).flatMap (fun job => job.ops.map (·.id))
  let accepted := localIds ++ backIds
  t.ok "all accepted jobs remain either committed or in their real FIFO"
    (trace.length + waiting.length == accepted.length &&
      accepted.all (fun id => trace.contains id != waiting.contains id))
  t.ok "busy accounting retains every queued job after actual loop service"
    ((← w.busy.get) == waiting.length && !queued.isEmpty)

/-- One real service iteration: checkpoint order and pause are unchanged. -/
def turnBehavior (t : Checks) (dir : String) : IO Unit := do
  let (_, db) ← database (dir ++ "/turn")
  let w ← writer
  let first := root "selected before checkpoint"
  let later := root "submitted by checkpoint callback"
  w.submit ⟨[first], true⟩
  w.save (checkpoint 91)
  let checkpointFirst ← IO.mkRef false
  let picked ← w.turn db fun db bytes => do
    Lifecycle.save db bytes
    let notYet := !(← valid db first)
    checkpointFirst.modify (fun _ => notYet)
    w.submit ⟨[later], true⟩
  t.ok "actual turn commits checkpoint before its already selected job"
    ((← checkpointFirst.get) && picked.any (fun j => j.ops.map (·.id) == [first.id]) &&
      (← valid db first) && !(← valid db later))
  discard <| w.turn db Lifecycle.save
  t.ok "arrival during checkpoint cannot replace the selected job or disappear"
    ((← valid db later) && (← w.busy.get) == 0 && (← w.jobs.get).isEmpty)
  w.setPaused true
  let held := root "paused queue remains owned"
  w.submit ⟨[held], true⟩
  w.save (checkpoint 92)
  let .none ← w.turn db Lifecycle.save | throw (IO.userError "paused turn selected a job")
  t.ok "pause keeps accepted jobs queued while allowing the checkpoint to commit"
    (!(← valid db held) && (← w.busy.get) == 1 && !(← w.jobs.get).isEmpty && (← w.saveDone))
  w.setPaused false
  discard <| w.turn db Lifecycle.save
  t.ok "resume applies the retained job and balances busy accounting"
    ((← valid db held) && (← w.busy.get) == 0 && (← w.jobs.get).isEmpty)
  -- Empty preferred classes fall back in the same actual turn.
  let onlyBack := root "background fallback"
  w.submit ⟨[onlyBack], false⟩
  discard <| w.turn db Lifecycle.save
  t.ok "an empty local class never wastes a background service turn" (← valid db onlyBack)

end WriterFairness

unsafe def main (args : List String) : IO Unit := do
  let dir := args.headD "out/writer-fairness/data"
  let t ← Checks.new
  WriterFairness.oppositeLaneSharing t
  WriterFairness.runningLoop t dir
  WriterFairness.turnBehavior t dir
  let code ← t.finish "writer-fairness"
  (← IO.getStdout).flush
  -- The intentionally continuing production writer remains paused and owned.
  IO.Process.exit code.toUInt8
