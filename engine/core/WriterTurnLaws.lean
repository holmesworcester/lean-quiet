/- The writer's turn (engine/core/WriterTurn.lean), run with a recording
interpreter: the queue, the pending checkpoint and the readers'
acknowledgement given, the store committing or refusing, every call
recorded. -/
import engine.core.WriterTurn

namespace Engine.Writer

/-- A call a turn made. -/
inductive Event (J : Type) where
  | asked
  | commit (c : Commit J)
  | committed (c : Commit J)
  | refused (c : Commit J)
  | idle

/-- The writer's operations, recorded. -/
def record {J : Type} (next : Option J) (save : Option (Nat × ByteArray × Bool)) (due : Option Nat)
    (ok : Bool) : Ops (StateM (List (Event J))) J where
  take := pure next
  pending := pure save
  pruneDue := do modify (· ++ [.asked]); pure due
  commit c := do modify (· ++ [.commit c]); pure ok
  committed c _ := modify (· ++ [.committed c])
  refused c := modify (· ++ [.refused c])
  idle := modify (· ++ [.idle])

/-- The commits a run made. -/
def commits {J : Type} (t : List (Event J)) : List (Commit J) :=
  t.filterMap fun | .commit c => some c | _ => none

variable {J : Type} (next : Option J) (save : Option (Nat × ByteArray × Bool)) (due : Option Nat) (ok : Bool)

/-- The calls one turn makes. -/
def trace : List (Event J) := ((turn (record next save due ok)).run []).2

/-- **A turn commits at most once**: its job, its checkpoint and its
prune go in one transaction. -/
theorem commits_once : (commits (trace next save due ok)).length ≤ 1 := by
  cases next <;> cases save <;> cases due <;> cases ok <;>
    simp [trace, turn, record, plan, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] <;> split <;> simp_all

/-- **A job's turn never prunes**: with a job selected, the turn does not
even ask how far the readers are, and its commit prunes nothing. -/
theorem job_no_prune (j : J) :
    Event.asked ∉ trace (some j) save due ok ∧ ∀ c ∈ commits (trace (some j) save due ok), c.prune = none := by
  cases save <;> cases ok <;>
    simp [trace, turn, record, plan, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] <;> split <;> simp_all

/-- **A checkpoint handed over rides the next turn**, job or not, unless
a refused turn held it back. -/
theorem save_rides (n : Nat) (b : ByteArray) :
    ∃ c ∈ commits (trace next (some (n, b, false)) due ok), c.save = some b := by
  cases next <;> cases due <;> cases ok <;>
    simp [trace, turn, record, plan, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- **A held-back checkpoint never rides with a job**, so a checkpoint
that keeps failing never takes a job down with it again. -/
theorem held_not_with_job (j : J) (n : Nat) (b : ByteArray) :
    ∀ c ∈ commits (trace (some j) (some (n, b, true)) due ok), c.save = none := by
  cases ok <;>
    simp [trace, turn, record, plan, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- **A held-back checkpoint rides the next idle turn.** Jobs come first:
under a writer that never idles (a long sync) it waits, and a crash in
that window restores the checkpoint before it; the writer counts its
held-back checkpoints (`Data.Writer.held`), so one that waits is seen. -/
theorem held_rides_idle (n : Nat) (b : ByteArray) :
    ∃ c ∈ commits (trace (none : Option J) (some (n, b, true)) due ok), c.save = some b := by
  cases due <;> cases ok <;>
    simp [trace, turn, record, plan, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- **An idle turn prunes what the readers acknowledged.** -/
theorem idle_prunes (q : Nat) :
    ∃ c ∈ commits (trace (none : Option J) save (some q) ok), c.prune = some q := by
  cases save <;> cases ok <;>
    simp [trace, turn, record, plan, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- The calls the shipped writer's turn makes. -/
def traceShipped : List (Event J) := ((turnShipped (record next save due ok)).run []).2

/-- The control: the shipped writer commits a checkpoint and a job in
two transactions. -/
theorem shipped_commits_twice (j : J) (n : Nat) (b : ByteArray) (held : Bool) :
    (commits (traceShipped (some j) (some (n, b, held)) due true)).length = 2 := by
  simp [traceShipped, turnShipped, record, commits, StateT.run, bind, StateT.bind, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

end Engine.Writer
