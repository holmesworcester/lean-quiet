/-
Where everything sits on the screen, and the proof that list content is
never covered.

The screen, top to bottom: the header (`top` rows from the top edge), the
viewport, the composer (`bot` rows), then whichever is taller of the
navigation bar and the keyboard. The list is bottom-anchored: content at
distance p above its end is drawn at screen row `composerTop - 1 - (p - b)`
for offset b.

The app draws the list frame for an offset `bf` (frame row r shows the
content at `bf + view + over - 1 - r`, Seam.frameRow). Surface.make calls
these functions and publishes cropped rectangles to every shell. They
copy those numbers; Surface.published_row connects the serialized
rectangle to the row proved here, for rows inside its clip and UInt32 bounds.
Slide.edge_eq and Translate.equivariance extend this to native vsyncs;
Translate.pinned states that pinned pages do not move. The theorems:

- `placed_row`: frame row r lands where content `frameRow r` belongs for the
  vsync's offset: the slide and the keyboard shift are exactly right.
- `visible_in_viewport`: content within [bn, bn + viewport height) lands
  inside the viewport: below the header, above the composer and keyboard.
- `newest_visible`: pinned to the newest message (bn = 0), a last row that
  fits in the viewport is wholly visible: no row of it is under the
  composer or the header.

These functions run through Surface.make and Session.present on every
platform. Native buffer copying, compositor application and OS event
acquisition remain trusted; native code no longer chooses placement.
-/
namespace Geometry

/-- The screen as the app sees it each frame. -/
structure Geom where
  h : Nat
  insetBot : Nat
  ime : Nat
  top : Nat
  bot : Nat
  deriving Inhabited, BEq, Repr

/-- How far the keyboard pushes the composer above the navigation bar. -/
def Geom.shift (g : Geom) : Nat := g.ime - g.insetBot

/-- The composer's top row: the viewport's bottom edge. -/
def Geom.composerTop (g : Geom) : Nat := g.h - g.bot - max g.insetBot g.ime

/-- The viewport's height with the keyboard closed: what the app draws
the list frame for. -/
def Geom.view (g : Geom) : Nat := g.h - g.top - g.bot - g.insetBot

/-- The viewport's height now (the keyboard takes its shift off it). -/
def Geom.viewNow (g : Geom) : Nat := g.composerTop - g.top

/-- The screen leaves room for the viewport. -/
def Geom.Fits (g : Geom) : Prop := g.top + g.bot + max g.insetBot g.ime ≤ g.h

namespace Seam

/-- The content distance frame row r shows, for a frame drawn at offset bf
(the platform seam's definition; negative is background). -/
def frameRow (g : Geom) (over bf r : Nat) : Int := (bf : Int) + g.view + over - 1 - r

/-- Where the twin places frame row r of a frame drawn at bf, at a vsync
whose offset is bn: the frame's first row is `over` rows above the
viewport's top, slid by the offset's change, and lifted by the keyboard. -/
def place (g : Geom) (over bf bn r : Nat) : Int :=
  (g.top : Int) - over + r + ((bn : Int) - bf) - g.shift

/-- Where content at distance p belongs, at offset bn. -/
def home (g : Geom) (bn : Nat) (p : Int) : Int := (g.composerTop : Int) - 1 - (p - bn)

end Seam

open Seam

theorem view_shift (g : Geom) (hf : g.Fits) :
    (g.top : Int) + g.view - g.shift = g.composerTop := by
  unfold Geom.view Geom.shift Geom.composerTop Geom.Fits at *
  have : max g.insetBot g.ime = g.insetBot + (g.ime - g.insetBot) := by omega
  omega

/-- **The slide and the keyboard shift are exact.** Frame row r, drawn at
bf and placed at a vsync with offset bn, lands exactly where the content
it shows belongs at bn. -/
theorem placed_row (g : Geom) (hf : g.Fits) (over bf bn r : Nat) :
    place g over bf bn r = home g bn (frameRow g over bf r) := by
  unfold place home frameRow
  have := view_shift g hf
  omega

/-- **Nothing on screen is covered.** Content within the viewport's
height of the offset lands strictly below the header and strictly above
the composer (and so above the keyboard and the navigation bar). -/
theorem visible_in_viewport (g : Geom) (hf : g.Fits) (bn : Nat) (p : Int)
    (lo : (bn : Int) ≤ p) (hi : p < bn + g.viewNow) :
    (g.top : Int) ≤ home g bn p ∧ home g bn p < g.composerTop := by
  unfold home Geom.viewNow Geom.composerTop Geom.Fits at *
  omega

/-- **Pinned, the newest message is wholly visible.** At offset 0, a last
row from `pad` to `pad + h` above the content's end that fits in the
viewport has every pixel row inside it: none under the composer, none
under the header. -/
theorem newest_visible (g : Geom) (hf : g.Fits) (pad h : Nat) (fit : pad + h ≤ g.viewNow)
    (k : Nat) (hk : k < h) :
    (g.top : Int) ≤ home g 0 (pad + k) ∧ home g 0 (pad + k) < g.composerTop :=
  visible_in_viewport g hf 0 (pad + k) (by omega) (by omega)

/-- And the frame row that shows it is one the twin places there. -/
theorem newest_drawn (g : Geom) (hf : g.Fits) (over pad h : Nat) (fit : pad + h ≤ g.viewNow)
    (r : Nat) (hr : frameRow g over 0 r = pad + h - 1) (hh : 0 < h) :
    (g.top : Int) ≤ place g over 0 0 r ∧ place g over 0 0 r < g.composerTop := by
  rw [placed_row g hf, hr]
  exact visible_in_viewport g hf 0 _ (by omega) (by omega)

/-! ## Pages: pinned to the top

A page (Get started, Create, Paste, …) is drawn into the list layer from
its top, at offset 0, and the twin places such a frame *pinned*: no slide,
and no lift by the keyboard (`Seam.pinned`). The keyboard then covers the
page's lower rows and moves nothing. Lifting it, as a conversation is
lifted, pushed a page's heading and controls off the top of the screen;
these say that cannot happen. -/

namespace Seam

/-- Where the twin places row r of a pinned frame. -/
def pinned (g : Geom) (over r : Nat) : Int := (g.top : Int) - over + r

/-- The page row a pinned frame's row r shows (a page is drawn at offset
0, its row k at frame row over + k). -/
def pageRow (over r : Nat) : Int := (r : Int) - over

/-- The page row the app takes a list tap to be on: the twin reports a
tap on a pinned frame as `composerTop + shift - 1 - y` (the keyboard
closed's composer top), and the app reads row `view - 1 - p`. -/
def tapRow (g : Geom) (y : Nat) : Int :=
  (g.view : Int) - 1 - ((g.composerTop : Int) + g.shift - 1 - y)

end Seam

/-- **A page row is where the page put it**, whatever the keyboard does:
row k of the page at screen row top + k. -/
theorem pinned_row (g : Geom) (over r : Nat) :
    pinned g over r = (g.top : Int) + pageRow over r := by
  unfold pinned pageRow; omega

/-- **The keyboard covers a page; it never pushes it.** Page content
above the keyboard's top (row k < the viewport's height now) lands below
the header and above the composer: on screen. -/
theorem pinned_visible (g : Geom) (over k : Nat) (hk : k < g.viewNow) :
    (g.top : Int) ≤ pinned g over (over + k) ∧ pinned g over (over + k) < g.composerTop := by
  unfold pinned Geom.viewNow at *; omega

/-- **A tap on a page lands on the row drawn under it**, keyboard open or
not. -/
theorem pinned_tap (g : Geom) (hf : g.Fits) (y : Nat) :
    tapRow g y = (y : Int) - g.top := by
  have := view_shift g hf
  unfold tapRow; omega

end Geometry
