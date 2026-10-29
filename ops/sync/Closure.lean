/-
Admission to a window's requirement walk. Each distinct id occupies one
slot, pending or visited. Overflow keeps the admitted prefix and reports
it; no discarded id is marked visited. Laws are in ClosureLaws.
-/
import ops.sync.Memory
import engine.core.Model

namespace Engine.Sync

/-- Distinct ids, retaining the last occurrence's order. -/
def closureIds : List Id → List Id
  | [] => []
  | i :: ids =>
    let rest := closureIds ids
    if rest.contains i then rest else i :: rest

/-- Admit fresh requirements into the remaining closure slots. -/
def queueClosure (cap : Nat) (closed : Std.HashSet Id) (frontier ids : List Id) : List Id × Bool :=
  let fresh := closureIds (ids.filter fun i => !closed.contains i && !frontier.contains i)
  let room := cap - (closed.size + frontier.length)
  (frontier ++ fresh.take room, Decidable.decide (room < fresh.length))

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] (fam : Family F)

/-- The stored ops of room r reached from `todo` through requirements,
each id visited once, in visiting order, at most `fuel` of them. An op
of another room, or an id not stored, is not followed. -/
def closureOps (r : Id) (fuel : Nat) (todo seen : List Id) : m (List Op) :=
  match fuel, todo with
  | 0, _ => pure []
  | _, [] => pure []
  | n + 1, y :: rest =>
    if has seen y then closureOps r (n + 1) rest seen
    else do
      match ← Store.getOp (F := F) y with
      | some o =>
        if fam.room o = some r then
          return o :: (← closureOps r n (o.reqs ++ rest) (y :: seen))
        else closureOps r n rest (y :: seen)
      | none => closureOps r n rest (y :: seen)
termination_by (fuel, todo.length)

@[simp] theorem closureOps_nil (r : Id) (fuel : Nat) (seen : List Id) :
    (closureOps fam r fuel [] seen : m (List Op)) = pure [] := by
  cases fuel <;> rw [closureOps]; simp

end

end Engine.Sync
