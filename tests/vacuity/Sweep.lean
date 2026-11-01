import engine.sync.SweepRun
import tests.vacuity.Network

/- Synthetic nonempty payload and a populated held store. These checks exercise
the production cursor and its actual store interpreter, not native SQLite,
membership signatures, socket admission or whole-app convergence. -/
namespace Vacuity.Sweep
open Engine Engine.Sync
open Vacuity.Network (msg fam)
attribute [local instance] byteArray_lawfulBEq

def cursor : Engine.Sync.Sweep := ⟨0, 1, true⟩
def visible (_ : Op) : Bool := true
def held : Held Unit :=
  { log := [msg], db := { DB.empty with ops := fun id => if id == msg.id then some msg else none } }

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

theorem readOnlyRun :
    (cursor.run (Catalog.held fam) visible maxFrame).run held =
      (cursor.step (Sweep.observedCeiling (Catalog.held fam) cursor held)
        (Sweep.observedInput (Catalog.held fam) cursor held) visible maxFrame, held) :=
  Sweep.run_observed _ _ _ _ _ rfl (fun _ => rfl)

theorem heldRun :
    (cursor.run (Catalog.held fam) visible maxFrame).run held =
      (cursor.step (Sweep.observedCeiling (Catalog.held fam) cursor held)
        (Sweep.observedInput (Catalog.held fam) cursor held) visible maxFrame, held) :=
  Sweep.held_run_observed fam cursor visible maxFrame held

theorem existingRow : ((Catalog.held fam).read 1).run held = (some msg.id, held) := rfl

theorem exactInput : Sweep.observedInput (Catalog.held fam) cursor held = some msg := by
  simp [Sweep.observedInput, cursor, Sweep.begin,
    Catalog.held, Catalog.shared, fam, oneRoom, Family.room, held, HeldM.run]

theorem exactOutput :
    (cursor.run (Catalog.held fam) visible maxFrame).run held =
      ((⟨1, 1, true⟩, some msg), held) := by
  rw [heldRun, exactInput]
  simp [Sweep.step, Sweep.next, Sweep.offer, Sweep.begin, Sweep.advance,
    cursor, visible, fits, Nat.not_lt.mpr fits]

-- More recent insertions do not extend the captured high-water mark, and a
-- full socket does not silently skip the row. Revocation suppresses output.
example : (Sweep.step cursor 500 (some msg) visible 0).1 = cursor := by decide +kernel
example : (Sweep.step cursor 500 (some msg) (fun _ => false) maxFrame).2 = none := by decide +kernel
example : (Sweep.step cursor 500 (some msg) visible maxFrame).1.high = 1 := by decide +kernel

end Vacuity.Sweep
