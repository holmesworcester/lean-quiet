/-
Coverage over RGBX rows, clipped with signed coordinates before indexing.
Bold takes the maximum of neighbouring coverage rather than repeatedly
blending an edge. No native text drawing is involved.
-/
import Quiet.Ttf.Raster

namespace Ttf

def blit (g : Bitmap) (rows : Array ByteArray) (x y : Nat) (color : UInt32) (smear : Nat) : Array ByteArray := Id.run do
  let mut rows := rows
  for gy in [0:g.h] do
    let py := (y : Int) + g.y + (gy : Int)
    if py < 0 then continue
    rows := rows.modify py.toNat fun row => Id.run do
      let mut row := row
      for gx in [0:g.w + smear] do
        let px := (x : Int) + g.x + (gx : Int)
        if px < 0 then continue
        let at_ := 4 * px.toNat
        if at_ + 3 ≥ row.size then continue
        let mut alpha := 0
        for k in [0:smear + 1] do
          if gx ≥ k && gx - k < g.w then
            if h : gy * g.w + gx - k < g.pixels.size then
              alpha := max alpha g.pixels[gy * g.w + gx - k].toNat
        if alpha == 0 then continue
        for ch in [0:3] do
          if h : at_ + ch < row.size then
            let src := ((color >>> ((2 - ch) * 8).toUInt32) &&& 255).toNat
            let dst := row[at_ + ch].toNat
            row := row.set (at_ + ch) (((src * alpha + dst * (255 - alpha) + 127) / 255).toUInt8) h
      return row
  return rows

end Ttf
