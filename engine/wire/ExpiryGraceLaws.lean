import engine.wire.ExpiryGrace
import engine.wire.IngressChurnLaws

namespace Engine.Sync.ExpiryGrace

theorem same_generation (amount : Nat) (s : State) (pending : Bool) :
    check amount s.heard true pending (some s) = (pending && s.left != 0, some s) := by
  simp [check]

theorem no_rearm (amount : Nat) (s : State) (pending : Bool) :
    (check amount s.heard true pending (some s)).2 = some s := by
  rw [same_generation]

theorem exhausted (amount heard : Nat) (pending : Bool) :
    (check amount heard true pending (some ⟨heard, 0⟩)).1 = false := by
  rw [same_generation amount ⟨heard, 0⟩ pending]
  cases pending <;> rfl

theorem empty_no_delay (amount heard : Nat) (overdue : Bool) (old : Option State) :
    (check amount heard overdue false old).1 = false := by
  simp only [check]
  split <;> simp

theorem fresh_clears (amount heard : Nat) (pending : Bool) (old : Option State) :
    check amount heard false pending old = (false, none) := by rfl

theorem consume_keeps_generation (s : State) : (consume s).heard = s.heard := rfl

theorem consume_decreases (s : State) (h : 0 < s.left) : (consume s).left < s.left := by
  simp only [consume]
  omega

theorem consume_saturates (heard : Nat) : consume ⟨heard, 0⟩ = ⟨heard, 0⟩ := rfl

def consumed : Nat → State → State
  | 0, s => s
  | n + 1, s => consume (consumed n s)

theorem consumed_left (n : Nat) (s : State) : (consumed n s).left = s.left - n := by
  induction n with
  | zero => simp [consumed]
  | succ n ih => simp only [consumed, consume, ih]; omega

theorem budget_exhausted (n heard : Nat) :
    (consumed (budget n) ⟨heard, budget n⟩).left = 0 := by
  simp [consumed_left]

/-- Reuse the actual prioritized source bound, including unrelated source
retirement/reuse. Before the selected turn, its one-shot budget is positive;
that turn handles the source before the subsequent expiry decision. Explicit
retirement is deliberately an alternative, never delayed by this policy. -/
theorem source_before_exhaustion {W E : Type} {n : Nat}
    (r : Ingress.Prioritized.ChurnRun W E n) (i : Nat)
    (target : Fin (n + 1)) (value : E) (heard : Nat)
    (ready : (r.state i).inbox.slots[target.val] = some value) :
    ∃ j, i ≤ j ∧ j < i + budget n ∧
      0 < (consumed (j-i) ⟨heard, budget n⟩).left ∧
      (r.selected j = some (.inr (target, value)) ∨ target ∈ r.closed j) := by
  obtain ⟨j, hi, hj, hs⟩ := Ingress.Prioritized.source_or_cancelled_within r i target value ready
  refine ⟨j, hi, hj, ?_, hs⟩
  rw [consumed_left]
  simp only [budget]
  omega

end Engine.Sync.ExpiryGrace
