/-
Binarization: which pixels of a camera frame are dark.

A single threshold fails under a phone's uneven light, so the threshold is
local (the scheme of ZXing's hybrid binarizer): the frame is cut into 8×8
blocks; each block's black point is its mean, or, for a flat block (range
of 24 or less), half its minimum, raised to its neighbours' black point
when that is above its minimum (so a flat block inside a dark area stays
dark and one inside a light area stays light). A pixel is dark when it is
at or below the mean black point of the 5×5 blocks around its own.
Frames smaller than 40 pixels a side take the mean of the frame.

The result is a `Bits`: one byte a pixel, 1 dark. Every read is `a[i]?`.
-/
import engine.renderer.qr.Encode

namespace Qr

/-- A binarized frame. -/
structure Bits where
  w : Nat
  h : Nat
  b : ByteArray

namespace Bits

@[inline] def dark (m : Bits) (x y : Nat) : Bool :=
  x < m.w && y < m.h && bget m.b (y * m.w + x) != 0

/-- Dark at a real-valued point (the pixel it falls in); outside is light. -/
@[inline] def darkAt (m : Bits) (x y : Float) : Bool :=
  if x < 0 || y < 0 || x ≥ m.w.toFloat || y ≥ m.h.toFloat then false
  else m.dark x.toUInt64.toNat y.toUInt64.toNat

def invert (m : Bits) : Bits :=
  { m with b := ⟨m.b.data.map (fun v => if v == 0 then 1 else 0)⟩ }

end Bits

@[inline] def Image.lum (img : Image) (x y : Nat) : Nat := (bget img.px (y * img.stride + x)).toNat

/-- Whether the frame's buffer holds all its rows. -/
def Image.wellFormed (img : Image) : Bool :=
  img.w > 0 && img.h > 0 && img.stride ≥ img.w && img.w ≤ 16384 && img.h ≤ 16384 &&
    img.px.size ≥ (img.h - 1) * img.stride + img.w

/-- Dark where at or below the frame's mean. -/
def globalBits (img : Image) : Bits := Id.run do
  let mut sum := 0
  for y in [0:img.h] do
    for x in [0:img.w] do
      sum := sum + img.lum x y
  let t := sum / (img.w * img.h).max 1
  let mut b := ByteArray.emptyWithCapacity (img.w * img.h)
  for y in [0:img.h] do
    for x in [0:img.w] do
      b := b.push (if img.lum x y ≤ t then 1 else 0)
  return { w := img.w, h := img.h, b }

/-- Local thresholds over 8×8 blocks (see the module comment). -/
def hybridBits (img : Image) : Bits := Id.run do
  let w := img.w
  let h := img.h
  if w < 40 || h < 40 then return globalBits img
  let sw := (w + 7) / 8
  let sh := (h + 7) / 8
  -- black points
  let mut bp : Array Nat := Array.replicate (sw * sh) 0
  for by_ in [0:sh] do
    let y0 := min (by_ * 8) (h - 8)
    for bx in [0:sw] do
      let x0 := min (bx * 8) (w - 8)
      let mut sum := 0
      let mut lo := 255
      let mut hi := 0
      for dy in [0:8] do
        for dx in [0:8] do
          let v := img.lum (x0 + dx) (y0 + dy)
          sum := sum + v
          lo := min lo v
          hi := max hi v
      let mut avg := sum / 64
      if hi - lo ≤ 24 then
        avg := lo / 2
        if by_ > 0 && bx > 0 then
          let nb := (bp[(by_ - 1) * sw + bx]?.getD 0 + 2 * bp[by_ * sw + bx - 1]?.getD 0 +
            bp[(by_ - 1) * sw + bx - 1]?.getD 0) / 4
          if lo < nb then avg := nb
      bp := bp.setIfInBounds (by_ * sw + bx) avg
  -- thresholds, then pixels
  let mut out := ByteArray.mk (Array.replicate (w * h) 0)
  for by_ in [0:sh] do
    let y0 := min (by_ * 8) (h - 8)
    let cy := min (max by_ 2) (sh - 3)
    for bx in [0:sw] do
      let x0 := min (bx * 8) (w - 8)
      let cx := min (max bx 2) (sw - 3)
      let mut sum := 0
      for j in [0:5] do
        for i in [0:5] do
          sum := sum + bp[(cy + j - 2) * sw + (cx + i - 2)]?.getD 0
      let t := sum / 25
      for dy in [0:8] do
        for dx in [0:8] do
          let x := x0 + dx
          let y := y0 + dy
          if img.lum x y ≤ t then out := bset out (y * w + x) 1
  return { w, h, b := out }

end Qr
