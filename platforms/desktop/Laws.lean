/-
The desktop root's laws over App's running frame.

- `settled_no_hold`: once `framePainted` holds (what `settleFrame` waits for
  after a resize), no position of the list frame App.listFrame draws
  shows a row's placeholder: the frame shown at a new size is never one
  whose rows flash to placeholders.
-/
import platforms.desktop.Driver

namespace Desktop

/-- **A settled frame holds no placeholder.** -/
theorem settled_no_hold (s : App.St) (h : framePainted s = true) (hc : s.page = .chat)
    (pad bottom : Nat) (more : Bool) (p j : Nat) :
    Cover.seen pad bottom more (App.frameSlice s s.b (App.bottoms s).1).2.1.toList p ≠ .hold j := by
  apply Cover.painted_no_hold
  intro r hr
  unfold framePainted at h
  simp only [hc, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at h
  have := (Array.all_eq_true_iff_forall_mem.1 h.1) r (by simpa using hr)
  simpa using this

end Desktop
