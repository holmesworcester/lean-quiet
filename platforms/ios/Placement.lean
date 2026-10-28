/-
How the iOS twin (ios/quiet_ios.m) places the list frame, and that this
is Geometry's placement: Seam.place for a conversation, Seam.pinned for a
page, and a page's taps reported as pinned_tap reads them.

UIKit does the placing. The list frame is a layer in the content of an
upside-down scroll view, whose content y is the distance above the
content's end, so content distance d is drawn at screen row
`bottom - 1 - (d - offset)` (`shown`), where `bottom` is the scroll view's
bottom edge on screen and `offset` its content offset. A tap at screen row
y is reported as the content distance under it (`tapped`). The twin
chooses only the bottom edge and the offset:

- a conversation: the bottom edge on the composer, which the keyboard
  lifts (`g.composerTop`), and the offset b the OS scrolls to;
- a page: the bottom edge where the composer is with the keyboard closed
  (a layout guide: the safe area's bottom less the composer's height,
  `closed_bottom`), and offset 0.

The trusted step is UIKit's: that a layer in a scroll view flipped
upside down lands at `shown`, and a tap is located at `tapped`.
-/
import engine.renderer.Geometry

namespace Geometry.Ios

open Seam

/-- Where content distance d is drawn, in a scroll view whose bottom edge is
screen row `bottom`, scrolled to `offset`. -/
def shown (bottom offset : Nat) (d : Int) : Int := (bottom : Int) - 1 - (d - offset)

/-- What a tap at screen row y reports: the content distance under it. -/
def tapped (bottom offset y : Nat) : Int := (bottom : Int) - 1 - y + offset

/-- **A conversation's frame lands where Seam.place puts it** (and so,
by placed_row, where its content belongs). -/
theorem conversation (g : Geom) (hf : g.Fits) (over bf bn r : Nat) :
    shown g.composerTop bn (frameRow g over bf r) = place g over bf bn r := by
  rw [placed_row g hf]
  rfl

/-- The page's bottom edge, the keyboard-closed composer top, is the safe
area's bottom less the composer's height: the guide the twin lays out. -/
theorem closed_bottom (g : Geom) (hf : g.Fits) :
    ((g.composerTop + g.shift : Nat) : Int) = (g.h : Int) - g.insetBot - g.bot := by
  have := view_shift g hf
  unfold Geom.view Geom.Fits at *
  omega

/-- **A page lands where Seam.pinned puts it**: frame row r at the
viewport's top - over + r, so page row k at the top + k (pinned_row),
whatever the keyboard does. -/
theorem page (g : Geom) (hf : g.Fits) (over r : Nat) :
    shown (g.composerTop + g.shift) 0 (frameRow g over 0 r) = pinned g over r := by
  have := view_shift g hf
  unfold shown frameRow pinned
  omega

/-- **A tap on a page reports what pinned_tap reads**: the twin's report is
`composerTop + shift - 1 - y`, and the app takes it to page row y - top,
the row drawn there. -/
theorem page_tap (g : Geom) (hf : g.Fits) (y : Nat) :
    tapped (g.composerTop + g.shift) 0 y = (g.composerTop : Int) + g.shift - 1 - y ∧
    tapRow g y = (y : Int) - g.top := by
  refine ⟨?_, pinned_tap g hf y⟩
  unfold tapped
  omega

end Geometry.Ios

#print axioms Geometry.Ios.conversation
#print axioms Geometry.Ios.closed_bottom
#print axioms Geometry.Ios.page
#print axioms Geometry.Ios.page_tap
