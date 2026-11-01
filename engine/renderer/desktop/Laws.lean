/-
Laws of the running desktop tracks and control list: overlay containment,
minimum widths, monotone pane count, and contained 24px targets. They are
stated over `zoomLayout`, the tracks the desktop Driver paints and hits
(platforms/desktop/Driver.lean), at every density `dpi`. Widths are device
pixels: n CSS pixels are `(n * dpi + 80) / 160`, n itself at 160 dpi
(`zoom_identity`). Painting and dispatch consume the same filtered list.
No claim about glyph pixels or the inherited phone page controls is made here.
-/
import engine.renderer.desktop.Layout

namespace Desktop

/-- Navigation and the wider of conversation/drawer cover the window,
at every density. The drawer deliberately overlaps; it is not a third
partition. -/
theorem widths (w dpi : Nat) (opened : Bool) :
    (zoomLayout w opened dpi).nav.w + max (zoomLayout w opened dpi).main.w
      (zoomLayout w opened dpi).context.w = w := by
  by_cases hw : (720 * dpi + 80) / 160 ≤ w <;> cases opened <;> simp [zoomLayout, *] <;> omega

/-- Navigation abuts the conversation; the overlay ends at the right edge. -/
theorem adjacent (w dpi : Nat) (opened : Bool) :
    (zoomLayout w opened dpi).nav.x = 0 ∧
    (zoomLayout w opened dpi).nav.x + (zoomLayout w opened dpi).nav.w =
      (zoomLayout w opened dpi).main.x ∧
    max ((zoomLayout w opened dpi).main.x + (zoomLayout w opened dpi).main.w)
      ((zoomLayout w opened dpi).context.x + (zoomLayout w opened dpi).context.w) = w := by
  by_cases hw : (720 * dpi + 80) / 160 ≤ w <;> cases opened <;> simp [zoomLayout, *] <;> omega

/-- Opening settings on a wide desktop window preserves the conversation
and navigation geometry, and therefore does not force its text or
attachments to reflow. -/
theorem drawer_preserves_main (w dpi : Nat) (hw : (720 * dpi + 80) / 160 ≤ w) :
    (zoomLayout w true dpi).main = (zoomLayout w false dpi).main ∧
    (zoomLayout w true dpi).nav = (zoomLayout w false dpi).nav := by simp [zoomLayout, hw]

/-- On a wide window the drawer starts at or right of the conversation's
start and ends at the window's right edge. -/
theorem overlay_contained (w dpi : Nat) (hw : (720 * dpi + 80) / 160 ≤ w) :
    (zoomLayout w true dpi).main.x ≤ (zoomLayout w true dpi).context.x ∧
    (zoomLayout w true dpi).context.x + (zoomLayout w true dpi).context.w = w := by
  simp [zoomLayout, hw]; omega

/-- At supported widths (320 CSS pixels and up, at this density), each
non-collapsed surface has usable width: navigation 220 CSS pixels, the
conversation and the drawer 275. -/
theorem minimum (w dpi : Nat) (opened : Bool) (hw : (320 * dpi + 80) / 160 ≤ w) :
    ((zoomLayout w opened dpi).nav.w = 0 ∨
      (220 * dpi + 80) / 160 ≤ (zoomLayout w opened dpi).nav.w) ∧
    ((zoomLayout w opened dpi).main.w = 0 ∨
      (275 * dpi + 80) / 160 ≤ (zoomLayout w opened dpi).main.w) ∧
    ((zoomLayout w opened dpi).context.w = 0 ∨
      (275 * dpi + 80) / 160 ≤ (zoomLayout w opened dpi).context.w) := by
  by_cases hb : (720 * dpi + 80) / 160 ≤ w <;> cases opened <;> simp [zoomLayout, *] <;> omega

/-- A wider window never shows fewer panes, at any width and density. -/
theorem monotone (a b dpi : Nat) (opened : Bool) (hab : a ≤ b) :
    (zoomLayout a opened dpi).count ≤ (zoomLayout b opened dpi).count := by
  by_cases ha2 : (720 * dpi + 80) / 160 ≤ a <;> by_cases hb2 : (720 * dpi + 80) / 160 ≤ b <;>
    cases opened <;> simp [zoomLayout, Layout.count, *] <;>
    (repeat split) <;> omega

/-- Every control actually emitted by the root is contained in its pane
and has a hit area at least 24 by 24 logical pixels. -/
theorem controls_fit (g : Layout) (h : Nat) (xs : List (Control α))
    (c : Control α) (hc : c ∈ controls g h xs) : Fits g h c.pane c.box := by
  simpa [controls] using (List.mem_filter.mp hc).2

/-- Every emitted control lies wholly on screen, at every density. -/
theorem controls_screen (w h dpi : Nat) (opened : Bool) (xs : List (Control α))
    (c : Control α) (hc : c ∈ controls (zoomLayout w opened dpi) h xs) :
    c.box.x + c.box.w ≤ w ∧ c.box.y + c.box.h ≤ h := by
  have hf := controls_fit _ _ _ _ hc
  rcases hf with ⟨_, hx, hy, _⟩
  have ht : (zoomLayout w opened dpi |>.track c.pane).x +
      (zoomLayout w opened dpi |>.track c.pane).w ≤ w := by
    by_cases h2 : (720 * dpi + 80) / 160 ≤ w <;>
      cases c.pane <;> cases opened <;> simp [Layout.track, zoomLayout, *] <;> omega
  exact ⟨Nat.le_trans hx ht, hy⟩

/-- A hit names a member of the exact list the painter traverses. -/
theorem hit_drawn (xs : List (Control α)) (x y : Nat) (c : Control α)
    (hc : hit xs x y = some c) : c ∈ xs := by
  exact List.mem_of_find?_eq_some hc

/-- The guards admit real controls at the desktop breakpoint, at 150%
(240 dpi): the settings drawer's close button. -/
theorem witness :
    let c : Control Nat := ⟨.context, ⟨520, 0, 24, 24⟩, 0, "Close"⟩
    c ∈ controls (zoomLayout 1080 true 240) 480 [c] := by decide

end Desktop
