/-
The Surface scrim. Repaint glyph strokes against their shaded grounds
after compositing the scrim, so dimming cannot make visible text illegible.
The row layout must keep later pictures off text (the layout owner's law).
-/
import Quiet.Paint

namespace Scrim
open Paint

def pixel (c : Color) : Color := mixC c (Palette.color .dark .scrim) 154

def row (r : ByteArray) : ByteArray := Id.run do
  let mut out := r
  for x in [0:r.size / 4] do out := setPx out x (pixel (getPx r x))
  return out

def shade (b : Bitmap) : Bitmap := Id.run do
  let mut out := { b with rows := b.rows.map row, strokes := #[] }
  for s in b.strokes do
    let ground := row s.ground
    let ink := pixel s.ink
    out := { out with strokes := out.strokes.push { s with ground, ink } }
    out := out.modify s.y fun r => Id.run do
      let mut r := r
      for i in [0:s.n] do
        if s.bits &&& (0x8000000000000000 >>> i.toUInt64) != 0 then
          r := setPx r (s.x + i) (textColor ink ground i)
      return r
  return out

/-- Visible text under the Surface scrim keeps 4.5:1 against its
composited ground, for any input pixel, not just the palette swatches. -/
theorem legible (wanted : Color) (ground : ByteArray) (x : Nat) :
    Contrast.meets (textColor (pixel wanted) (row ground) x) (getPx (row ground) x) :=
  Contrast.ink_meets _ _

end Scrim
