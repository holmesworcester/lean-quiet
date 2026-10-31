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
import engine.renderer.desktop.Scrollbar

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

/-! ## The scrollbar: placed by rank, inside its track

`Scrollbar.layout` is what the desktop paints and hit-tests. Each law is
about the bar it returns, for whatever counts the app gives it. -/

section Bar

/-- **The thumb lies in the track, which is the viewport's height, and is
at least a target tall (or the whole track).** -/
theorem thumb_in_track {right top height content n k r dpi : Nat} {bar : Scrollbar.Bar}
    (h : Scrollbar.layout right top height content n k r dpi = some bar) :
    bar.track.y = top ∧ bar.track.h = height ∧ top ≤ bar.thumb.y ∧
    bar.thumb.y + bar.thumb.h ≤ top + height ∧ min ((24 * dpi + 80) / 160) height ≤ bar.thumb.h := by
  unfold Scrollbar.layout at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    have f := _root_.Scrollbar.inside height ((24 * dpi + 80) / 160) n (min k n)
      (min r (n - min k n)) (Nat.min_le_right _ _)
    have g := _root_.Scrollbar.size_le height ((24 * dpi + 80) / 160) n (min k n)
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · simp only; omega
    · simp only; omega
    · unfold _root_.Scrollbar.size
      exact Nat.le_min.2 ⟨Nat.min_le_right _ _, Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)⟩

/-- **At the newest message the thumb rests on the track's bottom.** -/
theorem newest_bottom {right top height content n k dpi : Nat} {bar : Scrollbar.Bar}
    (h : Scrollbar.layout right top height content n k 0 dpi = some bar) :
    bar.thumb.y + bar.thumb.h = bar.track.y + bar.track.h := by
  unfold Scrollbar.layout at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    have g := _root_.Scrollbar.size_le height ((24 * dpi + 80) / 160) n (min k n)
    simp [_root_.Scrollbar.newest_bottom]
    omega

/-- **With the oldest message on screen the thumb touches the track's top.** -/
theorem oldest_top {right top height content n k dpi : Nat} {bar : Scrollbar.Bar}
    (hk : k < n) (h : Scrollbar.layout right top height content n k (n - k) dpi = some bar) :
    bar.thumb.y = bar.track.y := by
  unfold Scrollbar.layout at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    have := _root_.Scrollbar.oldest_top height ((24 * dpi + 80) / 160) n k hk
    have g := _root_.Scrollbar.size_le height ((24 * dpi + 80) / 160) n k
    have e : min k n = k := Nat.min_eq_left (Nat.le_of_lt hk)
    have e' : min (n - k) (n - k) = n - k := Nat.min_self _
    simp only [e, e']
    omega

/-- **Further back in the conversation, the thumb is higher.** -/
theorem thumb_monotone {right top height content n k r r' dpi : Nat} {bar bar' : Scrollbar.Bar}
    (hr : r ≤ r') (h : Scrollbar.layout right top height content n k r dpi = some bar)
    (h' : Scrollbar.layout right top height content n k r' dpi = some bar') :
    bar'.thumb.y ≤ bar.thumb.y := by
  unfold Scrollbar.layout at h h'
  dsimp only at h h'
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    split at h'
    · simp at h'
    · simp only [Option.some.injEq] at h'
      subst h h'
      have m := _root_.Scrollbar.monotone height ((24 * dpi + 80) / 160) n (min k n)
        (r := min r (n - min k n)) (r' := min r' (n - min k n)) (by omega)
      have f := _root_.Scrollbar.inside height ((24 * dpi + 80) / 160) n (min k n)
        (min r (n - min k n)) (Nat.min_le_right _ _)
      have f' := _root_.Scrollbar.inside height ((24 * dpi + 80) / 160) n (min k n)
        (min r' (n - min k n)) (Nat.min_le_right _ _)
      simp only
      omega

/-- **A drag never lands the thumb above the pointer**: after seeking, the
thumb's offset from the track's bottom is at most the pointer's. -/
theorem drag_below (b : Scrollbar.Bar) (grab y : Nat) :
    _root_.Scrollbar.place (b.track.h - b.thumb.h) (b.n - b.k) (Scrollbar.seek b grab y) ≤
      (b.track.h - b.thumb.h) - min (b.track.h - b.thumb.h) (y - min grab b.thumb.h - b.track.y) :=
  _root_.Scrollbar.seek_below _ _ _

/-- **Dragging higher seeks further back.** -/
theorem drag_mono (b : Scrollbar.Bar) (grab : Nat) {y y' : Nat} (h : y ≤ y') :
    Scrollbar.seek b grab y' ≤ Scrollbar.seek b grab y := by
  unfold Scrollbar.seek
  apply _root_.Scrollbar.seek_mono
  omega

end Bar

end Desktop
