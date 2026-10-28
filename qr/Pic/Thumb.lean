/-
Scaling a picture down (for thumbnails): each output pixel is the mean of
a 4×4 grid of source points spread over its footprint. The output is
built with `Array.ofFn`, so its size is `4 * tw * th` by construction
(`scale_wellFormed`); reads are `b[i]?` with a default.
-/
import Pic.Qoi

namespace Pic

/-- `src` scaled to `tw × th`. -/
def scale (src : Rgba) (tw th : Nat) : Rgba :=
  let px := Array.ofFn (n := 4 * tw * th) fun i =>
    let k := i.val
    let c := k % 4
    let x := k / 4 % tw.max 1
    let y := k / 4 / tw.max 1
    -- source points: (x + (2u + 1) / 8) · w / tw for u < 4, likewise rows
    Id.run do
      let mut s := 0
      for v in [0:4] do
        for u in [0:4] do
          let sx := ((8 * x + 2 * u + 1) * src.w) / (8 * tw.max 1)
          let sy := ((8 * y + 2 * v + 1) * src.h) / (8 * th.max 1)
          s := s + (get8 src.px (4 * (sy * src.w + sx) + c)).toNat
      return (s / 16).toUInt8
  { w := tw, h := th, px := ⟨px⟩ }

end Pic
