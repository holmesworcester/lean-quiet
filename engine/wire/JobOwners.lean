/- Bounded ownership of the original native tasks, independent of a successful
Loop.turn return. Only completion of that original task permits reclamation. -/
import Std.Sync.Mutex

namespace Engine.Sync

structure NativeJob where
  cancel : IO Unit
  done : Task (Except IO.Error Unit)

structure JobOwners where
  cap : Nat
  jobs : Std.Mutex (List NativeJob)

/-- A live reservation may overlap its original dial and socket jobs during
the completion-event handoff. Both original tasks remain owned. -/
def JobOwners.socketCapacity (maxSocks : Nat) : Nat := 2 * maxSocks

def JobOwners.new (cap : Nat) : IO JobOwners := do
  return ⟨cap, ← Std.Mutex.new []⟩

/-- The cap decision used before starting either socket task or a dial. -/
def JobOwners.room {α : Type} (cap : Nat) (jobs : List α) : Bool := jobs.length < cap

/-- Runtime-called effectful gate: a full table does not evaluate the factory. -/
def JobOwners.admit {α β : Type} {m : Type → Type} [Monad m]
    (cap : Nat) (jobs : List α) (create : m β) : m (Option β) :=
  if room cap jobs then some <$> create else pure none

/-- Creation is BaseIO: no recoverable exception can strand a task between its
creation and registration. The actual closures only start dedicated tasks and
construct their handles; native I/O and cancellation run outside this mutex. -/
def JobOwners.launch {α : Type} (owners : JobOwners)
    (create : BaseIO (α × NativeJob)) : IO (Option α) := owners.jobs.atomically do
  let retained ← (← getThe (List NativeJob)).filterM fun j => return !(← IO.hasFinished j.done)
  set retained
  let result ← admit owners.cap retained create
  match result with
  | none => return none
  | some (value, job) =>
    set (job :: retained)
    return some value

/-- Snapshot ownership before requesting cancellation. No registry lock is
held while touching a source/outbox; one failed request cannot skip the rest. -/
def JobOwners.request (owners : JobOwners) : IO Unit := do
  let jobs ← owners.jobs.atomically (getThe (List NativeJob))
  for j in jobs do discard <| j.cancel.toBaseIO

/-- Called after the loop cannot register more work. Retain original task
handles through completion, including reader cleanup and socket-slot release. -/
def JobOwners.join (owners : JobOwners) : IO Unit := do
  let jobs ← owners.jobs.atomically (getThe (List NativeJob))
  for j in jobs do discard <| IO.wait j.done
  owners.jobs.atomically (set ([] : List NativeJob))

end Engine.Sync
