/-
The desktop root's laws over App's running frame.

- `pinned_bottom`: pinned to the newest message, the scrollbar's thumb rests
  on the bottom of its track (the bar App's state gives `Desktop.scrollbar`).
- `settled_no_hold`: once `framePainted` holds (what `settleFrame` waits for
  after a resize), no position of the list frame App.listFrame draws
  shows a row's placeholder: the frame shown at a new size is never one
  whose rows flash to placeholders.
-/
import platforms.desktop.Driver
import engine.renderer.desktop.Laws

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

/-- **Pinned to the newest message, the thumb rests on the track's bottom**:
the bar `Desktop.scrollbar` returns for the running app. -/
theorem pinned_bottom (g : Layout) (s : App.St) (bar : Scrollbar.Bar) (hb : s.b = 0)
    (h : scrollbar g s = some bar) :
    bar.thumb.y + bar.thumb.h = bar.track.y + bar.track.h := by
  unfold scrollbar at h
  split at h
  · simp at h
  · have hr := _root_.Scrollbar.ranks_newest (column s) (App.geom s).viewNow (by show 0 < 12; decide)
    rcases hq : _root_.Scrollbar.ranks (column s) s.b (App.geom s).viewNow with ⟨n, k, r⟩
    rw [hb] at hq h
    rw [hq] at hr h
    simp only at hr
    subst hr
    exact newest_bottom h

end Desktop
