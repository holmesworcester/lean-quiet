/-
The Surface scrim. Repaint glyph strokes against their shaded grounds
after compositing the scrim, so dimming cannot make visible text illegible.
The row layout must keep later pictures off text (the layout owner's law).
-/
import engine.renderer.Paint

namespace Scrim
open Paint

def pixel (c : Color) : Color := mixC c (Palette.color .dark .scrim) 154

def row (r : ByteArray) : ByteArray := Id.run do
  let mut out := r
  for x in [0:r.size / 4] do out := setPx out x (pixel (getPx r x))
  return out

def shade (b : Bitmap) : Bitmap := Id.run do
  -- Undo text in reverse paint order, retaining photographs and other ground.
  let mut out := { b with strokes := #[] }
  for s in b.strokes.reverse do
    out := out.modify s.y fun r => Id.run do
      let mut r := r
      for i in [0:s.n] do
        if s.alpha i > 0 then
          r := setPx r (s.x+i) (getPx (if s.under.isEmpty then s.ground else s.under) i)
      return r
  out := { out with rows := out.rows.map row }
  -- Then repaint in order. Adjacent Arabic/italic glyphs can overlap;
  -- each resolves ink against its line's ground and blends over prior ink.
  for s in b.strokes do
    let ground := row s.ground
    let ink := pixel s.ink
    let under := (out.rows[s.y]?.getD .empty).extract (4*s.x) (4*(s.x+s.n))
    let stroke := { s with ground, ink, under }
    out := { out with strokes := out.strokes.push stroke }
    out := out.modify s.y fun r => Id.run do
      let mut r := r
      for i in [0:s.n] do
        if s.alpha i > 0 then r := setPx r (s.x+i) (stroke.color i)
      return r
  return out

/-- Visible text under the Surface scrim keeps 4.5:1 against its
composited ground, for any input pixel, not just the palette swatches. -/
theorem legible (wanted : Color) (ground : ByteArray) (x : Nat) :
    Contrast.meets (textColor (pixel wanted) (row ground) x) (getPx (row ground) x) :=
  Contrast.ink_meets _ _

end Scrim
