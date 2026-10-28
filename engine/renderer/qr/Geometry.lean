/-
Plane geometry for sampling: a homography from module coordinates
(column, row; module (c, r) spans [c, c+1] × [r, r+1]) to image pixels,
fitted by least squares to point pairs.

A fit is the direct linear transform with the last entry fixed at 1,
solved by Gaussian elimination with partial pivoting on Hartley-normalized
coordinates (so the normal equations stay well conditioned). Three pairs
give an affine map; four or more a full homography. A singular system is
`none`.
-/
namespace Qr

structure Pt where
  x : Float
  y : Float
  deriving Inhabited

namespace Pt
def add (a b : Pt) : Pt := ⟨a.x + b.x, a.y + b.y⟩
def sub (a b : Pt) : Pt := ⟨a.x - b.x, a.y - b.y⟩
def scale (k : Float) (a : Pt) : Pt := ⟨k * a.x, k * a.y⟩
def dist (a b : Pt) : Float := Float.sqrt ((a.x - b.x) ^ 2 + (a.y - b.y) ^ 2)
def d2 (a b : Pt) : Float := (a.x - b.x) ^ 2 + (a.y - b.y) ^ 2
end Pt

/-- A 3×3 matrix, row-major. -/
abbrev M3 := Array Float

def M3.get (m : M3) (i j : Nat) : Float := m[3 * i + j]?.getD 0

def M3.mul (a b : M3) : M3 := Id.run do
  let mut r : Array Float := Array.mkEmpty 9
  for i in [0:3] do
    for j in [0:3] do
      r := r.push (a.get i 0 * b.get 0 j + a.get i 1 * b.get 1 j + a.get i 2 * b.get 2 j)
  return r

/-- A homography: module coordinates to pixels. -/
structure Homography where
  m : M3

def Homography.apply (t : Homography) (u v : Float) : Pt :=
  let w := t.m.get 2 0 * u + t.m.get 2 1 * v + t.m.get 2 2
  let w := if w.abs < 1e-12 then 1e-12 else w
  ⟨(t.m.get 0 0 * u + t.m.get 0 1 * v + t.m.get 0 2) / w,
   (t.m.get 1 0 * u + t.m.get 1 1 * v + t.m.get 1 2) / w⟩

/-- Solves `a x = b` (a is n×n, row-major) by Gaussian elimination with
partial pivoting; `none` if singular. -/
def solve (n : Nat) (a : Array Float) (b : Array Float) : Option (Array Float) := Id.run do
  let mut a := a
  let mut b := b
  let g (a : Array Float) (i j : Nat) : Float := a[i * n + j]?.getD 0
  for col in [0:n] do
    -- pivot
    let mut piv := col
    let mut best := (g a col col).abs
    for r in [col + 1:n] do
      if (g a r col).abs > best then
        best := (g a r col).abs
        piv := r
    if best < 1e-12 then return none
    if piv != col then
      for j in [0:n] do
        let t := g a col j
        a := a.setIfInBounds (col * n + j) (g a piv j)
        a := a.setIfInBounds (piv * n + j) t
      let t := b[col]?.getD 0
      b := b.setIfInBounds col (b[piv]?.getD 0)
      b := b.setIfInBounds piv t
    let p := g a col col
    for r in [col + 1:n] do
      let f := g a r col / p
      if f != 0 then
        for j in [col:n] do
          a := a.setIfInBounds (r * n + j) (g a r j - f * g a col j)
        b := b.setIfInBounds r (b[r]?.getD 0 - f * b[col]?.getD 0)
  -- back substitution
  let mut x : Array Float := Array.replicate n 0
  for k in [0:n] do
    let i := n - 1 - k
    let mut s := b[i]?.getD 0
    for j in [i + 1:n] do
      s := s - g a i j * x[j]?.getD 0
    x := x.setIfInBounds i (s / g a i i)
  if x.any (fun v => v.isNaN || v.isInf) then return none
  return some x

/-- The similarity that moves points to their centroid and scales their
mean distance from it to √2, and its inverse. -/
def normalizer (ps : Array Pt) : M3 × M3 :=
  let n := ps.size.toFloat
  let n := if n == 0 then 1 else n
  let cx := ps.foldl (fun s p => s + p.x) 0 / n
  let cy := ps.foldl (fun s p => s + p.y) 0 / n
  let md := ps.foldl (fun s p => s + Float.sqrt ((p.x - cx) ^ 2 + (p.y - cy) ^ 2)) 0 / n
  let k := if md < 1e-9 then 1 else Float.sqrt 2 / md
  (#[k, 0, -k * cx, 0, k, -k * cy, 0, 0, 1], #[1 / k, 0, cx, 0, 1 / k, cy, 0, 0, 1])

/-- The least-squares homography (affine with three pairs) taking each
`src` point to its `dst`. -/
def fitHomography (src dst : Array Pt) : Option Homography := do
  let np := min src.size dst.size
  if np < 3 then none
  let (ts, _) := normalizer (src.extract 0 np)
  let (td, tdInv) := normalizer (dst.extract 0 np)
  let nu := (src.extract 0 np).map fun p => (ts.get 0 0 * p.x + ts.get 0 2, ts.get 1 1 * p.y + ts.get 1 2)
  let nx := (dst.extract 0 np).map fun p => (td.get 0 0 * p.x + td.get 0 2, td.get 1 1 * p.y + td.get 1 2)
  let k := if np ≥ 4 then 8 else 6
  -- normal equations AᵀA h = Aᵀb
  let mut ata : Array Float := Array.replicate (k * k) 0
  let mut atb : Array Float := Array.replicate k 0
  for i in [0:np] do
    let (u, v) := nu[i]?.getD (0, 0)
    let (x, y) := nx[i]?.getD (0, 0)
    let rx : Array Float := if k == 8 then #[u, v, 1, 0, 0, 0, -u * x, -v * x] else #[u, v, 1, 0, 0, 0]
    let ry : Array Float := if k == 8 then #[0, 0, 0, u, v, 1, -u * y, -v * y] else #[0, 0, 0, u, v, 1]
    for a in [0:k] do
      for b in [0:k] do
        ata := ata.modify (a * k + b) (· + (rx[a]?.getD 0) * (rx[b]?.getD 0) + (ry[a]?.getD 0) * (ry[b]?.getD 0))
      atb := atb.modify a (· + (rx[a]?.getD 0) * x + (ry[a]?.getD 0) * y)
  let h ← solve k ata atb
  let g (i : Nat) := h[i]?.getD 0
  let hn : M3 := #[g 0, g 1, g 2, g 3, g 4, g 5, (if k == 8 then g 6 else 0), (if k == 8 then g 7 else 0), 1]
  let m := M3.mul tdInv (M3.mul hn ts)
  let s := m.get 2 2
  if s.abs < 1e-12 then none
  pure ⟨m.map (· / s)⟩

end Qr
