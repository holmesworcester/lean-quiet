import engine.sync.SweepRun
import tests.vacuity.Network

/- Synthetic nonempty payload. These checks exercise the production cursor's
transition. The running sweep step over the SQLite catalog is that
transition (`sql_run_step`): its evidence runs on a real SQLite file in
tests/vacuity/StoreTrust.lean. Not membership signatures, socket admission
or whole-app convergence. -/
namespace Vacuity.Sweep
open Engine Engine.Sync
open Vacuity.Network (msg fam)
attribute [local instance] byteArray_lawfulBEq

def cursor : Engine.Sync.Sweep := ⟨0, 1, true⟩
def visible (_ : Op) : Bool := true
theorem fits : Sweep.cost msg ≤ maxFrame := by decide +kernel

theorem progress :
    (Sweep.step cursor 500 (some msg) visible maxFrame).2 = some msg ∨
      Sweep.rank 1 (Sweep.step cursor 500 (some msg) visible maxFrame).1 < Sweep.rank 1 cursor :=
  Sweep.step_progress (by decide) (by intro h; cases h)
    (by intro _ _; rfl) rfl fits (Nat.le_refl _)

theorem stalled :
    Sweep.rank 1 (Sweep.step cursor 500 (some msg) visible 0).1 ≤ Sweep.rank 1 cursor :=
  Sweep.step_nonincrease (by decide) (by intro h; cases h)
    (by intro _ _; rfl) rfl fits (by decide +kernel)

/-- A history: the cursor stepped on, with the message at position 1 of a
one-row catalog, a full frame each tick. -/
def history : Nat → Engine.Sync.Sweep
  | 0 => {}
  | n + 1 => (Sweep.step (history n) 1 (some msg) visible maxFrame).1

/-- The message is offered on every pass, from any start. -/
theorem retriedFair : ∀ start, ∃ n, start ≤ n ∧
    (Sweep.step (history n) 1 (some msg) visible maxFrame).2 = some msg :=
  Sweep.retried_fair history (fun _ => 1) (fun _ => maxFrame) (fun _ => some msg) (fun _ => visible)
    msg 1 (by decide) fits (fun _ => rfl) (fun _ _ => Nat.le_refl _) (fun _ _ _ => rfl)
    (fun _ => rfl) (fun start => ⟨start, Nat.le_refl _, Nat.le_refl _⟩)

-- The history has content: the first step offers the message, the next
-- finishes the pass, and the one after offers it again.
example : (Sweep.step (history 0) 1 (some msg) visible maxFrame).2 = some msg := by decide +kernel
example : (Sweep.step (history 1) 1 (some msg) visible maxFrame).2 = none := by decide +kernel
example : (Sweep.step (history 2) 1 (some msg) visible maxFrame).2 = some msg := by decide +kernel

-- More recent insertions do not extend the captured high-water mark, and a
-- full socket does not silently skip the row. Revocation suppresses output.
example : (Sweep.step cursor 500 (some msg) visible 0).1 = cursor := by decide +kernel
example : (Sweep.step cursor 500 (some msg) (fun _ => false) maxFrame).2 = none := by decide +kernel
example : (Sweep.step cursor 500 (some msg) visible maxFrame).1.high = 1 := by decide +kernel

end Vacuity.Sweep
