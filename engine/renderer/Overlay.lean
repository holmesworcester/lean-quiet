/-
Edges of Marks and Toast, resolved against the pixels actually covered.
Opaque inner fills isolate their text from Page, Chrome or Surface below.
Placement and whether an overlap is allowed belong to the layer table.
-/
import engine.renderer.Paint

namespace Overlay
open Paint

def edge (theme : Theme.Value) (under : Color) : Color :=
  Contrast.ink (Palette.color theme .edge) under

/-- The outside edge of an overlap meets 3:1 against any pixel beneath,
including images and already composited scrims. -/
theorem edge_contrast (theme : Theme.Value) (under : Color) :
    Contrast.meets (edge theme under) under 30 := Contrast.ink_control _ _

/-- Composite a toast row. Its corners are transparent, its edge reads
the destination, and its opaque interior keeps the text's own ground. -/
def toastRow (theme : Theme.Value) (dst src : ByteArray) (x y w h radius thickness : Nat) : ByteArray := Id.run do
  let mut out := dst
  for i in [0:w] do
    if cover 0 0 w h radius i y == 0 then continue
    let inside := thickness ≤ i && i < w - thickness && thickness ≤ y && y < h - thickness &&
      cover thickness thickness (w - thickness) (h - thickness) (radius - thickness) i y == 256
    let c := if inside then getPx src i else edge theme (getPx dst (x+i))
    out := setPx out (x+i) c
  return out

/-- A badge with a visible outer edge on its own host. -/
def badge (theme : Theme.Value) (b : Bitmap) (x y w h radius thickness : Nat) : Bitmap := Id.run do
  let src := solid (Palette.color theme .badge) w
  let mut b := b
  for j in [0:h] do
    b := b.modify (y+j) fun dst => toastRow theme dst src x j w h radius thickness
  return b

end Overlay
