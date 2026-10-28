/-
Unhinted quadratic outlines, flattened to at most 1/256 pixel chord error,
then filled by nonzero winding on an 8 × 8 sample grid. The scanline
visits edges once per subrow, not once per pixel. Output includes explicit
ink overhangs; checked construction proves its extent and pixel count.
-/
import Quiet.Ttf.Read

namespace Ttf

structure Edge where
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float
  deriving Inhabited

private def midpoint (a b : Point) : Point :=
  ⟨(a.x + b.x) / 2, (a.y + b.y) / 2, true⟩

private def line (a b : Point) : Edge := ⟨a.x, a.y, b.x, b.y⟩

private def quad (a b c : Point) : Array Edge := Id.run do
  -- The quadratic's maximum deviation from a chord is |a-2b+c|/4.
  let bend := max (a.x - 2*b.x + c.x).abs (a.y - 2*b.y + c.y).abs
  let n := max 1 (min 128 ((bend * 64).sqrt.ceil.toUInt64.toNat))
  let mut out := #[]
  let mut prev := a
  for i in [1:n + 1] do
    let t := i.toFloat / n.toFloat
    let u := 1 - t
    let p : Point := ⟨u*u*a.x + 2*u*t*b.x + t*t*c.x, u*u*a.y + 2*u*t*b.y + t*t*c.y, true⟩
    out := out.push (line prev p)
    prev := p
  return out

/-- Insert implied on-curve midpoints, rotate to an on-curve point,
then consume on/off pairs. Every loop is bounded by the point count. -/
def edges (contour : Contour) : Array Edge := Id.run do
  if contour.isEmpty then return #[]
  let mut ps := #[]
  for i in [0:contour.size] do
    let some p := contour[i]? | return #[]
    let some q := contour[(i + 1) % contour.size]? | return #[]
    ps := ps.push p
    if !p.on && !q.on then ps := ps.push (midpoint p q)
  let some first := ps.findIdx? (·.on) | return #[]
  ps := ps.extract first ps.size ++ ps.extract 0 first
  let some start := ps[0]? | return #[]
  ps := ps.push start
  let mut prev := start
  let mut skip := false
  let mut out := #[]
  for i in [1:ps.size] do
    if skip then skip := false; continue
    let some p := ps[i]? | return #[]
    if p.on then
      out := out.push (line prev p)
      prev := p
    else
      let some q := ps[i + 1]? | return #[]
      out := out ++ quad prev p q
      prev := q
      skip := true
  return out

structure Bitmap where
  x : Int
  y : Int
  w : Nat
  h : Nat
  advance : Nat
  cell : Nat
  left : Nat
  right : Nat
  top : Nat
  bottom : Nat
  pixels : ByteArray
  deriving Inhabited

/-- An ink box may extend beyond its advance cell only by its declared
left/right/top/bottom overhang. The buffer has exactly one byte per pixel. -/
def Bitmap.Valid (b : Bitmap) : Prop :=
  b.pixels.size = b.w * b.h ∧
  -(b.left : Int) ≤ b.x ∧ b.x + (b.w : Int) ≤ (b.advance + b.right : Nat) ∧
  -(b.top : Int) ≤ b.y ∧ b.y + (b.h : Int) ≤ (b.cell + b.bottom : Nat)
  deriving Decidable

/-- Saturation is deliberate, even for adversarial winding counts. -/
def coverage (samples : Nat) : UInt8 := (min 255 (samples * 255 / 64)).toUInt8

/-- All consumers use this checked constructor. -/
def checked (b : Bitmap) : Option Bitmap := if b.Valid then some b else none

private def floorInt (x : Float) : Int := x.floor.toInt64.toInt
private def ceilInt (x : Float) : Int := x.ceil.toInt64.toInt

/-- A pixel can receive at most 64 samples. Writes use Array.modify,
which is itself bounds checked; reads are optional, never unchecked. -/
def rasterRaw (f : Face) (glyph size cell : Nat) : Option Bitmap := do
  if size == 0 || size > 256 || cell > 512 then failure
  let contours ← outline f glyph
  let scale := size.toFloat / f.units.toFloat
  let baseline := (cell * 4 / 5).toFloat
  let contours := contours.map (·.map fun p => { p with x := p.x * scale, y := baseline - p.y * scale })
  let mut xmin : Float := 0
  let mut xmax : Float := 0
  let mut ymin : Float := baseline
  let mut ymax : Float := baseline
  for c in contours do
    for p in c do
      if !p.x.isFinite || !p.y.isFinite || p.x.abs > 4096 || p.y.abs > 4096 then failure
      xmin := min xmin p.x
      xmax := max xmax p.x
      ymin := min ymin p.y
      ymax := max ymax p.y
  let x0 := floorInt xmin
  let y0 := floorInt ymin
  let w := (ceilInt xmax - x0).toNat
  let h := (ceilInt ymax - y0).toNat
  if w > 1024 || h > 1024 || w * h > 262144 then failure
  let allEdges := contours.foldl (fun acc c => acc ++ edges c) #[]
  let mut samples := Array.replicate (w * h) 0
  for row in [0:h] do
    for sy in [0:8] do
      let y := y0.toFloat + row.toFloat + (sy.toFloat + 0.5) / 8
      let mut crossings : Array (Float × Int) := #[]
      for e in allEdges do
        if (e.y0 ≤ y && y < e.y1) || (e.y1 ≤ y && y < e.y0) then
          crossings := crossings.push (e.x0 + (y - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0), if e.y1 > e.y0 then 1 else -1)
      crossings := crossings.qsort (fun a b => a.1 < b.1)
      let mut winding : Int := 0
      let mut left : Float := 0
      for (x, direction) in crossings do
        if winding != 0 then
          -- Samples at (k + .5)/8, in the half-open interval [left,x).
          let a := max 0 (ceilInt ((left - x0.toFloat) * 8 - 0.5))
          let z := min (w * 8 : Nat) (ceilInt ((x - x0.toFloat) * 8 - 0.5)).toNat
          for sx in [a.toNat:z] do
            samples := samples.modify (row * w + sx / 8) (· + 1)
        winding := winding + direction
        left := x
  let pixels := samples.foldl (fun b n => b.push (coverage n)) ByteArray.empty
  let advance := advance f glyph size
  return ⟨x0, y0, w, h, advance, cell, (-x0).toNat,
    (x0 + (w : Int) - (advance : Int)).toNat, (-y0).toNat,
    (y0 + (h : Int) - (cell : Int)).toNat, pixels⟩

def raster (f : Face) (glyph size cell : Nat) : Option Bitmap := do
  checked (← rasterRaw f glyph size cell)

end Ttf
