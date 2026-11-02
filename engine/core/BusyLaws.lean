/- The runner's store calls under a busy store: a call SQLite refuses as
busy is tried again, and nothing else changes. -/
import engine.core.Busy

namespace Engine.Store

variable {α : Type} {act : IO α} {w w' : Void IO.RealWorld}

/-- A call that returns gives its value. -/
theorem attempt_ok {a : α} (h : act w = .ok a w') : attempt act w = .ok (some a) w' := by
  show EST.tryCatch (EST.bind act fun a => fun w => .ok (some a) w) _ w = _
  simp only [EST.tryCatch, EST.bind, h]

/-- **A busy store is tried again, never a failure.** A call SQLite
refuses as busy or locked comes back as `none`: `retrying` pauses and
runs it again. -/
theorem attempt_busy {e : IO.Error} (h : act w = .error e w') (hb : busy e = true) :
    attempt act w = .ok none w' := by
  show EST.tryCatch (EST.bind act fun a => fun w => .ok (some a) w) _ w = _
  simp only [EST.tryCatch, EST.bind, h, hb, ↓reduceIte]
  rfl

/-- Any other failure is the call's own, unchanged. -/
theorem attempt_other {e : IO.Error} (h : act w = .error e w') (hb : busy e = false) :
    attempt act w = .error e w' := by
  show EST.tryCatch (EST.bind act fun a => fun w => .ok (some a) w) _ w = _
  simp only [EST.tryCatch, EST.bind, h, hb, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **An attempt never fails busy**, whatever the call does: so the
runner's store calls, all made through `retrying`, never end it on a
busy store. -/
theorem attempt_never_busy {e : IO.Error} (h : attempt act w = .error e w') : busy e = false := by
  cases hc : act w with
  | ok a w₁ => rw [attempt_ok hc] at h; cases h
  | error e₁ w₁ =>
    cases hb : busy e₁ with
    | true => rw [attempt_busy hc hb] at h; cases h
    | false => rw [attempt_other hc hb] at h; cases h; exact hb

/-- The control: the shipped runner let a busy error through. -/
theorem shipped_busy_escapes {e : IO.Error} (h : act w = .error e w') (hb : busy e = true) :
    ∃ e', attemptShipped act w = .error e' w' ∧ busy e' = true := by
  refine ⟨e, ?_, hb⟩
  show EST.bind act (fun a => fun w => .ok (some a) w) w = _
  simp only [EST.bind, h]

end Engine.Store
