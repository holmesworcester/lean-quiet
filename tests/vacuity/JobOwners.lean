import engine.wire.JobOwnersLaws

namespace Vacuity.JobOwners
open Engine.Sync.JobOwners

def worker : StateM Nat Nat := do
  modify (· + 1)
  return 7

theorem refused : (admit 1 [4] worker).run 8 = (none, 8) := by
  rw [full_refuses 1 [4] worker (by decide)]
  rfl

theorem accepted : (admit 2 [4] worker).run 8 = (some 7, 9) := by
  rw [available_creates 2 [4] worker (by decide)]
  rfl

theorem bounded : (7 :: [4]).length ≤ 2 :=
  admitted_bounded 2 [4] 7 (by decide)

end Vacuity.JobOwners
