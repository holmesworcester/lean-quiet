import engine.renderer.Hover

namespace Hover

theorem disabled (p : Context) (b : Box) : active p b false = false := by simp [active]
theorem absent (b : Box) (enabled : Bool) : active none b enabled = false := by simp [active]
theorem leave_clears (p : Context) : update p .leave = none := rfl
theorem blur_clears (p : Context) : update p .blur = none := rfl
theorem touch_clears (p : Context) : update p .touch = none := rfl

theorem active_iff (p : Context) (b : Box) (enabled : Bool) :
    active p b enabled = true ↔ enabled = true ∧ ∃ q, p = some q ∧ b.has q = true := by
  cases p <;> simp [active]

theorem active_inside (p : Context) (b : Box) (enabled : Bool) (h : active p b enabled = true) :
    ∃ q, p = some q ∧ b.x ≤ q.1 ∧ q.1 < b.x + b.w ∧ b.y ≤ q.2 ∧ q.2 < b.y + b.h := by
  obtain ⟨_, q, hq, hb⟩ := (active_iff _ _ _).mp h
  exact ⟨q, hq, by simpa [Box.has, Bool.and_eq_true, and_assoc] using hb⟩

theorem front_drawn (p : Context) (xs : List (α × Box)) (a : α × Box)
    (h : front p xs = some a) : a ∈ xs := List.mem_of_find?_eq_some h

/-- A containing overlay wins even when its descendants are disabled. -/
theorem overlay_blocks (p : Context) (a : α × Box) (rest : List (α × Box))
    (h : active p a.2 = true) : front p (a :: rest) = some a := by simp [front, h]

theorem local_inside (p : Context) (b : Box) (q : Point) (h : within p b = some q) :
    q.1 < b.w ∧ q.2 < b.h := by
  cases p with
  | none => simp [within] at h
  | some p =>
    simp only [within, Option.bind_some] at h
    split at h
    next hb =>
      simp only [Option.some.injEq] at h
      subst q
      simp [Box.has, Bool.and_eq_true] at hb
      omega
    next => simp at h

theorem disabled_rest (p : Context) (b : Box) (rest hovered : α) :
    choose p b false rest hovered = rest := by simp [choose, disabled]

theorem absent_rest (b : Box) (enabled : Bool) (rest hovered : α) :
    choose none b enabled rest hovered = rest := by simp [choose, absent]

theorem routed_head_blocks [BEq α] (p : Context) (a : α × Box) (rest : List (α × Box))
    (key : α) (inside : active p a.2 = true) (other : (a.1 == key) = false) :
    routed p (a :: rest) key = none := by
  simp [routed, overlay_blocks p a rest inside, other]

theorem grace_expires (started now : Nat) (h : started + 400 ≤ now) :
    graceLive started now = false := by simp [graceLive]; omega

theorem menu_reachable (origin p : Point) (box : Box) (h : box.has p = true) :
    toward origin p box = true := by simp [toward, h]

end Hover
