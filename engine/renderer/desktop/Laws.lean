/-
Laws of the running desktop tracks and control list: overlay containment,
minimum widths, monotone pane count, and contained 24px targets. Painting
and dispatch consume the same filtered list. No claim about glyph pixels
or the inherited phone page controls is made here.
-/
import engine.renderer.desktop.Layout

namespace Desktop

/-- Navigation and the wider of conversation/drawer cover the window.
The drawer deliberately overlaps; it is not a third partition. -/
theorem widths (w : Nat) (opened : Bool) :
    (layout w opened).nav.w + max (layout w opened).main.w
      (layout w opened).context.w = w := by
  by_cases hw : 720 ≤ w <;> cases opened <;> simp [layout, *] <;> omega

/-- Navigation abuts the conversation; the overlay ends at the right edge. -/
theorem adjacent (w : Nat) (opened : Bool) :
    (layout w opened).nav.x = 0 ∧
    (layout w opened).nav.x + (layout w opened).nav.w = (layout w opened).main.x ∧
    max ((layout w opened).main.x + (layout w opened).main.w)
      ((layout w opened).context.x + (layout w opened).context.w) = w := by
  by_cases hw : 720 ≤ w <;> cases opened <;> simp [layout, *] <;> omega

/-- Opening settings on desktop preserves the conversation geometry,
and therefore does not force its text or attachments to reflow. -/
theorem drawer_preserves_main (w : Nat) (hw : 720 ≤ w) :
    (layout w true).main = (layout w false).main ∧
    (layout w true).nav = (layout w false).nav := by simp [layout, hw]

theorem overlay_contained (w : Nat) (hw : 720 ≤ w) :
    (layout w true).main.x ≤ (layout w true).context.x ∧
    (layout w true).context.x + (layout w true).context.w = w := by
  simp [layout, hw]; omega

/-- At supported widths, each non-collapsed surface has usable width. -/
theorem minimum (w : Nat) (opened : Bool) (hw : 320 ≤ w) :
    ((layout w opened).nav.w = 0 ∨ 220 ≤ (layout w opened).nav.w) ∧
    ((layout w opened).main.w = 0 ∨ 275 ≤ (layout w opened).main.w) ∧
    ((layout w opened).context.w = 0 ∨ 275 ≤ (layout w opened).context.w) := by
  by_cases hb : 720 ≤ w <;> cases opened <;> simp [layout, *] <;> omega

theorem monotone (a b : Nat) (opened : Bool) (ha : 320 ≤ a) (hab : a ≤ b) :
    (layout a opened).count ≤ (layout b opened).count := by
  by_cases ha2 : 720 ≤ a <;> by_cases hb2 : 720 ≤ b <;>
    cases opened <;> simp [layout, Layout.count, *] <;>
    (repeat split) <;> omega

/-- Every control actually emitted by the root is contained in its pane
and has a hit area at least 24 by 24 logical pixels. -/
theorem controls_fit (g : Layout) (h : Nat) (xs : List (Control α))
    (c : Control α) (hc : c ∈ controls g h xs) : Fits g h c.pane c.box := by
  simpa [controls] using (List.mem_filter.mp hc).2

/-- Every emitted control lies wholly on screen. -/
theorem controls_screen (w h : Nat) (opened : Bool) (xs : List (Control α))
    (c : Control α) (hc : c ∈ controls (layout w opened) h xs) :
    c.box.x + c.box.w ≤ w ∧ c.box.y + c.box.h ≤ h := by
  have hf := controls_fit _ _ _ _ hc
  rcases hf with ⟨_, hx, hy, _⟩
  have ht : (layout w opened |>.track c.pane).x +
      (layout w opened |>.track c.pane).w ≤ w := by
    by_cases h2 : 720 ≤ w <;>
      cases c.pane <;> cases opened <;> simp [Layout.track, layout, *] <;> omega
  exact ⟨Nat.le_trans hx ht, hy⟩

/-- A hit names a member of the exact list the painter traverses. -/
theorem hit_drawn (xs : List (Control α)) (x y : Nat) (c : Control α)
    (hc : hit xs x y = some c) : c ∈ xs := by
  exact List.mem_of_find?_eq_some hc

/-- The guards admit real controls at the desktop breakpoint. -/
theorem witness :
    let c : Control Nat := ⟨.context, ⟨345, 0, 24, 24⟩, 0, "Close"⟩
    c ∈ controls (layout 720 true) 480 [c] := by decide

end Desktop
