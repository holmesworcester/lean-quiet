import engine.wire.LaneLaws

namespace Vacuity.FairScheduler
open Engine.Sync

-- Immediate fallback keeps throughput when either queue is empty.
example : (Inbox.next false popW (popE (E := String))).run (["only write"], []) =
    ((some (.inl "only write"), true), ([], [])) := rfl
example : (Inbox.next true (popW (W := String)) popE).run ([], ["only frame"]) =
    ((some (.inr "only frame"), false), ([], [])) := rfl
example : (Inbox.next true (popW (W := String)) (popE (E := String))).run ([], []) =
    ((none, false), ([], [])) := rfl

-- A positive-period clock: sample every 200ms, beginning before the first
-- deadline. Its entire infinite timestamp/update sequence is explicit.
def clock : Tick.Run 200 where
  now := fun i => 200 * i
  last := fun i => 200 * (i - 1)
  next := by
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      simp only [Nat.succ_sub_one]
      apply Eq.symm
      rw [Tick.due 200 (200 * i) (200 * (i + 1)) (by omega)]

theorem timerForever : ∀ N, ∃ i ≥ N,
    (Tick.next 200 (clock.last i) (clock.now i)).1 = true :=
  Tick.cofinal clock (by
    intro N bound
    refine ⟨N + bound, by omega, ?_⟩
    change bound ≤ 200 * (N + bound)
    omega)

example : Tick.next 200 1000 1199 = (false, 1000) := by decide
example : Tick.next 200 1000 1200 = (true, 1200) := by decide
example : Tick.next 200 1000 1200 ≠ (false, 1000) := by decide

end Vacuity.FairScheduler
