/-
Finding a symbol in a binarized frame and sampling its modules.

1. Finder patterns: rows are scanned for dark-light-dark-light-dark runs
   at 1:1:3:1:1; each hit is cross-checked down its column, along its row
   again and along the diagonal, and hits at the same place are merged
   (after ZXing's finder).
2. Three finders that best make a right isosceles triangle are taken; the
   one at the right angle is top-left, and the turn from it decides which
   of the others is top-right. (A mirror image comes out transposed; the
   decoder reads the transpose too.)
3. The module size is measured along the lines between finder centres
   (the dark-light-dark runs through each finder), which gives the
   symbol's size.
4. A first map from module coordinates to pixels is affine, from the three
   finder centres. The bottom-right alignment pattern is searched for
   around where it predicts, in growing windows, by matching the 5×5
   pattern through the map; with it the map becomes a homography, which
   predicts every other alignment pattern, each refined by a small search.
   The final homography is a least-squares fit to all the centres found.
5. Each module is sampled at nine points through the map (majority).

Every loop is a `for` over a bounded range, so a frame of any content
ends: at most 48 finder candidates are kept, at most 4 triangles and 3
sizes tried.
-/
import Qr.Binarize
import Qr.Geometry
import Qr.ReadGrid

namespace Qr

/-- A finder pattern candidate: centre, module size, and how many scan
lines confirmed it. -/
structure Finder where
  c : Pt
  size : Float
  count : Nat
  deriving Inhabited

/-- Whether five run lengths look like a finder's 1:1:3:1:1. -/
def finderRatio (sc : Array Nat) (tol : Float := 0.5) : Bool :=
  let g (i : Nat) := (sc[i]?.getD 0).toFloat
  let total := g 0 + g 1 + g 2 + g 3 + g 4
  if sc.any (· == 0) || total < 7 then false
  else
    let ms := total / 7
    let v := ms * tol
    (ms - g 0).abs < v && (ms - g 1).abs < v && (3 * ms - g 2).abs < 3 * v &&
      (ms - g 3).abs < v && (ms - g 4).abs < v

/-- Length of the run of `want`-coloured pixels from (x, y) stepping (dx,
dy), at most `cap`. -/
def runFrom (m : Bits) (x y : Int) (dx dy : Int) (want : Bool) (cap : Nat) : Nat := Id.run do
  let mut n := 0
  for k in [0:cap] do
    let px := x + dx * k
    let py := y + dy * k
    if px < 0 || py < 0 then break
    if m.dark px.toNat py.toNat != want then break
    n := n + 1
  return n

/-- Runs through (x, y) along (dx, dy): the five finder states and the
centre of the middle one, measured from both ends; `none` when a run is
cut by the frame's edge or longer than `maxCount`. -/
def crossRuns (m : Bits) (x y : Int) (dx dy : Int) (maxCount : Nat) : Option (Array Nat × Float) := do
  let lim := max m.w m.h
  if x < 0 || y < 0 || !m.dark x.toNat y.toNat then none
  -- backwards from the centre
  let c0 := runFrom m x y (-dx) (-dy) true lim
  let b1 := runFrom m (x - dx * c0) (y - dy * c0) (-dx) (-dy) false (maxCount + 1)
  if b1 == 0 || b1 > maxCount then none
  let b0 := runFrom m (x - dx * (c0 + b1)) (y - dy * (c0 + b1)) (-dx) (-dy) true (maxCount + 1)
  if b0 == 0 || b0 > maxCount then none
  -- forwards
  let c1 := runFrom m (x + dx) (y + dy) dx dy true lim
  let f1 := runFrom m (x + dx * (c1 + 1)) (y + dy * (c1 + 1)) dx dy false (maxCount + 1)
  if f1 == 0 || f1 > maxCount then none
  let f0 := runFrom m (x + dx * (c1 + 1 + f1)) (y + dy * (c1 + 1 + f1)) dx dy true (maxCount + 1)
  if f0 == 0 || f0 > maxCount then none
  let sc := #[b0, b1, c0 + c1, f1, f0]
  -- centre of the middle run, along the line, relative to (x, y)
  let off := ((c1 + 1).toFloat - c0.toFloat) / 2
  pure (sc, off)

/-- The scan-line hit `sc` ending before column `endX` of row `y`,
confirmed (or not) by cross-checks; its centre and module size. -/
def confirm (m : Bits) (sc : Array Nat) (y endX : Nat) : Option (Pt × Float) := do
  let total := sc.foldl (· + ·) 0
  let mid := sc[2]?.getD 0
  let cx := endX.toFloat - (sc[4]?.getD 0).toFloat - (sc[3]?.getD 0).toFloat - mid.toFloat / 2
  let xi : Int := cx.toUInt64.toNat
  -- down the column
  let (vs, voff) ← crossRuns m xi y 0 1 (mid + 2)
  let vt := vs.foldl (· + ·) 0
  if 5 * (if vt ≥ total then vt - total else total - vt) ≥ 2 * total || !finderRatio vs then none
  let cy := y.toFloat + voff + 0.5
  -- along the row again, through the corrected centre
  let yi : Int := cy.toUInt64.toNat
  let (hs, hoff) ← crossRuns m xi yi 1 0 (mid + 2)
  let ht := hs.foldl (· + ·) 0
  if 5 * (if ht ≥ total then ht - total else total - ht) ≥ 2 * total || !finderRatio hs then none
  let cx := xi.toNat.toFloat + hoff + 0.5
  -- the diagonal
  let (ds, _) ← crossRuns m (cx.toUInt64.toNat : Int) yi 1 1 (2 * mid + 2)
  if !finderRatio ds 0.75 then none
  pure (⟨cx, cy⟩, (vt + ht).toFloat / 14)

/-- Adds a confirmed centre: merged into a candidate at the same place and
of a similar module size, else a new candidate (at most 48). -/
def addCenter (fs : Array Finder) (c : Pt) (ms : Float) : Array Finder := Id.run do
  for i in [0:fs.size] do
    let f := fs[i]?.getD default
    if (c.x - f.c.x).abs ≤ ms && (c.y - f.c.y).abs ≤ ms then
      let d := (ms - f.size).abs
      if d ≤ 1 || d ≤ f.size then
        let n := f.count.toFloat
        let f' : Finder := {
          c := ⟨(n * f.c.x + c.x) / (n + 1), (n * f.c.y + c.y) / (n + 1)⟩
          size := (n * f.size + ms) / (n + 1)
          count := f.count + 1 }
        return fs.setIfInBounds i f'
  if fs.size < 48 then fs.push { c, size := ms, count := 1 } else fs

/-- Finder candidates of a frame. -/
def findFinders (m : Bits) : Array Finder := Id.run do
  let mut fs : Array Finder := #[]
  let step := if m.h > 800 then 2 else 1
  for yy in [0:(m.h + step - 1) / step] do
    let y := yy * step
    let mut sc : Array Nat := #[0, 0, 0, 0, 0]
    let mut st := 0
    for x in [0:m.w + 1] do
      let d := x < m.w && m.dark x y
      if d then
        if st % 2 == 1 then st := st + 1
        sc := sc.modify st (· + 1)
      else
        if st % 2 == 0 then
          if st == 4 then
            if finderRatio sc then
              match confirm m sc y x with
              | some (c, ms) =>
                fs := addCenter fs c ms
                sc := #[0, 0, 0, 0, 0]
                st := 0
              | none =>
                sc := #[sc[2]?.getD 0, sc[3]?.getD 0, sc[4]?.getD 0, 1, 0]
                st := 3
            else
              sc := #[sc[2]?.getD 0, sc[3]?.getD 0, sc[4]?.getD 0, 1, 0]
              st := 3
          else
            st := st + 1
            sc := sc.modify st (· + 1)
        else
          sc := sc.modify st (· + 1)
  return fs

end Qr
