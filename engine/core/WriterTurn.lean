/-
One turn of the app's writer (`Data.Writer.turn`, app/Commands.lean), over
its operations: the job queue, the newest checkpoint handed over, the
readers' acknowledged journal, and the store. It is generic in the monad
and the job, so its laws (engine/core/WriterTurnLaws.lean) run this same
turn with a recording interpreter that the app runs with SQLite.

One transaction a turn. The selected job's write turn carries the newest
checkpoint with it; with no job, the checkpoint and the journal prune go
in one transaction; so slow commits do not queue behind one another. A
turn whose commit carried a checkpoint and was refused holds the
checkpoint back: the next jobs commit alone, and the checkpoint goes in
the next idle turn, so a checkpoint that keeps failing never starves the
jobs.
-/
namespace Engine.Writer

/-- What one turn commits, in one transaction. -/
structure Commit (J : Type) where
  job : Option J
  save : Option ByteArray
  prune : Option Nat

/-- The writer's operations. -/
structure Ops (m : Type → Type) (J : Type) where
  /-- The next job, unless the writer is paused. -/
  take : m (Option J)
  /-- The newest checkpoint handed over and not yet committed, numbered,
  and whether a refused turn held it back. -/
  pending : m (Option (Nat × ByteArray × Bool))
  /-- How far both readers have acknowledged the journal, if further
  than the last prune. -/
  pruneDue : m (Option Nat)
  /-- One transaction; whether it committed. -/
  commit : Commit J → m Bool
  /-- After a commit: the job is done, the checkpoint (numbered) is
  saved, the journal is pruned that far. -/
  committed : Commit J → Option Nat → m Unit
  /-- After a refused commit: the job rejoins its queue, and a checkpoint
  it carried is held back. -/
  refused : Commit J → m Unit
  /-- Nothing to do: a short pause. -/
  idle : m Unit

/-- The plan of a turn: the selected job with the pending checkpoint
(unless held back); with no job, the checkpoint and the prune due. -/
def plan {J : Type} (next : Option J) (save : Option (Nat × ByteArray × Bool))
    (prune : Option Nat) : Commit J :=
  match next with
  | some j => { job := some j, save := save.bind fun (_, b, held) => if held then none else some b, prune := none }
  | none => { job := none, save := save.map fun (_, b, _) => b, prune }

/-- One writer turn: the plan, then at most one commit. -/
def turn {m : Type → Type} [Monad m] {J : Type} (o : Ops m J) : m (Option J) := do
  let next ← o.take
  let save ← o.pending
  let prune ← match next with
    | some _ => pure none
    | none => o.pruneDue
  let c := plan next save prune
  if c.job.isNone && c.save.isNone && c.prune.isNone then
    o.idle
    return none
  if ← o.commit c then
    o.committed c (if c.save.isSome then save.map (·.1) else none)
  else
    o.refused c
  return next

/-- The writer as it shipped: the checkpoint committed before the job,
in a transaction of its own, then the job in another; the journal
pruned by a thread of its own. Kept as the control (tests/wiring.txt):
`shipped_commits_twice`. -/
def turnShipped {m : Type → Type} [Monad m] {J : Type} (o : Ops m J) : m (Option J) := do
  let next ← o.take
  let save ← o.pending
  if let some (n, b, _) := save then
    if ← o.commit { job := none, save := some b, prune := none } then
      o.committed { job := none, save := some b, prune := none } (some n)
  match next with
  | none => o.idle
  | some j =>
    let c : Commit J := { job := some j, save := none, prune := none }
    if ← o.commit c then o.committed c none else o.refused c
  return next

end Engine.Writer
