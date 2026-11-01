import engine.wire.JobOwners

namespace Engine.Sync.JobOwners

/-- Inserting one original job after the actual gate stays within its cap. -/
theorem admitted_bounded {α : Type} (cap : Nat) (jobs : List α) (job : α)
    (h : room cap jobs = true) : (job :: jobs).length ≤ cap := by
  simp only [room, decide_eq_true_eq] at h
  simp only [List.length_cons]
  omega

/-- Refusal is pure: the supplied worker factory is not run. -/
theorem full_refuses {α β : Type} {m : Type → Type} [Monad m]
    (cap : Nat) (jobs : List α) (create : m β) (h : cap ≤ jobs.length) :
    admit cap jobs create = pure none := by
  simp [admit, room, Nat.not_lt.mpr h]

/-- Successful admission uses the exact supplied worker factory. -/
theorem available_creates {α β : Type} {m : Type → Type} [Monad m]
    (cap : Nat) (jobs : List α) (create : m β) (h : jobs.length < cap) :
    admit cap jobs create = some <$> create := by
  simp [admit, room, h]

end Engine.Sync.JobOwners
