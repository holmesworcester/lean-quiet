/-
The frame decoder: a grayscale frame to the symbol it shows.

`decode` binarizes the frame (local thresholds, then a global one if
that finds nothing), finds finder patterns, and for up to four finder
triangles and three candidate sizes builds the module map (Detect.lean),
samples the matrix and decodes it as is or mirrored (ReadGrid.lean). A
size the version information contradicts is resampled at the size it
gives. The first symbol that decodes (all Reed–Solomon blocks within
capacity, segments that parse) is the answer; otherwise `none`.

Total: no `partial`, no fuel, no unchecked index; the work is bounded by
the frame's pixel count times a constant.
-/
import engine.renderer.qr.Detect

namespace Qr

/-- Distance from `a` towards `b` (in steps of one pixel) until the
dark-light-dark runs through a finder end: 3.5 modules from its centre;
`none` if they do not end before `b`. -/
def runsToEdge (m : Bits) (a b : Pt) : Option Float := Id.run do
  let d := a.dist b
  if d < 1 then return none
  let ux := (b.x - a.x) / d
  let uy := (b.y - a.y) / d
  let mut st := 0
  for k in [0:d.toUInt64.toNat] do
    let t := k.toFloat
    let dk := m.darkAt (a.x + ux * t) (a.y + uy * t)
    if st == 0 && !dk then st := 1
    else if st == 1 && dk then st := 2
    else if st == 2 && !dk then return some (t - 0.5)
  return none

/-- Module size measured between finders `a` and `b`: the runs through
each, both ways (7 modules each). -/
def sizeBetween (m : Bits) (a b : Pt) : Option Float := do
  let far (p q : Pt) : Pt := ⟨2 * p.x - q.x, 2 * p.y - q.y⟩
  let r1 ← runsToEdge m a b
  let r2 ← runsToEdge m a (far a b)
  let r3 ← runsToEdge m b a
  let r4 ← runsToEdge m b (far b a)
  pure ((r1 + r2 + r3 + r4) / 14)

/-- The three finders as (top-left, top-right, bottom-left). -/
def orient (a b c : Finder) : Finder × Finder × Finder :=
  let dab := a.c.d2 b.c
  let dbc := b.c.d2 c.c
  let dac := a.c.d2 c.c
  -- the right angle is opposite the longest side
  let (tl, p, q) :=
    if dbc ≥ dab && dbc ≥ dac then (a, b, c)
    else if dac ≥ dab && dac ≥ dbc then (b, a, c)
    else (c, a, b)
  let cross := (p.c.x - tl.c.x) * (q.c.y - tl.c.y) - (p.c.y - tl.c.y) * (q.c.x - tl.c.x)
  if cross ≥ 0 then (tl, p, q) else (tl, q, p)

/-- Up to four finder triangles, the most right-isosceles first, of
candidates of similar module size. -/
def triangles (fs : Array Finder) : Array (Finder × Finder × Finder) := Id.run do
  let strong := fs.filter (·.count ≥ 2)
  let pool := if strong.size ≥ 3 then strong else fs
  let pool := (pool.qsort (fun a b => a.count > b.count)).extract 0 10
  let mut scored : Array (Float × (Finder × Finder × Finder)) := #[]
  for i in [0:pool.size] do
    for j in [i + 1:pool.size] do
      for k in [j + 1:pool.size] do
        let a := pool[i]?.getD default
        let b := pool[j]?.getD default
        let c := pool[k]?.getD default
        let lo := min a.size (min b.size c.size)
        let hi := max a.size (max b.size c.size)
        if hi ≤ 2 * lo then
          let (tl, tr, bl) := orient a b c
          let x := tl.c.d2 tr.c
          let y := tl.c.d2 bl.c
          let z := tr.c.d2 bl.c
          if z > 0 && x > 0 && y > 0 then
            -- legs equal and z = x + y
            let s := (z - x - y).abs / z + (x - y).abs / (x + y)
            -- legs at least ~7 modules long
            if s < 0.5 && x.sqrt > 7 * lo && y.sqrt > 7 * lo then
              scored := scored.push (s, (tl, tr, bl))
  return ((scored.qsort (fun a b => a.1 < b.1)).extract 0 4).map (·.2)

/-- Candidate sizes (modules a side) for a triangle and module size. -/
def sizeCandidates (tl tr bl : Pt) (ms : Float) : List Nat :=
  if ms ≤ 0 then []
  else
    let a := (tl.dist tr / ms).round
    let b := (tl.dist bl / ms).round
    let d := ((a + b) / 2).round.toUInt64.toNat + 7
    let d := match d % 4 with
      | 0 => d + 1
      | 2 => d - 1
      | 3 => d + 2
      | _ => d
    [d, d + 4, d - 4].filter (fun n => 21 ≤ n && n ≤ 177)

/-- The affine map that puts the finder centres at their module
coordinates. -/
def affineFor (tl tr bl : Pt) (n : Nat) : Option Homography :=
  let e := n.toFloat - 3.5
  fitHomography #[⟨3.5, 3.5⟩, ⟨e, 3.5⟩, ⟨3.5, e⟩] #[tl, tr, bl]

/-- How many of the 25 modules of an alignment pattern centred at module
coordinates (u, v), at scale `s`, have the colours one should. -/
def alignScore (m : Bits) (t : Homography) (u v s : Float) : Nat := Id.run do
  let mut n := 0
  for j in [0:5] do
    for i in [0:5] do
      let di := i.toFloat - 2
      let dj := j.toFloat - 2
      let p := t.apply (u + s * di) (v + s * dj)
      let want := max (if i ≥ 2 then i - 2 else 2 - i) (if j ≥ 2 then j - 2 else 2 - j) != 1
      if m.darkAt p.x p.y == want then n := n + 1
  return n

/-- Searches for an alignment pattern around module coordinates (u, v)
within `r` modules, in quarter-module steps, at scales `scales`: the
centroid (in pixels) of the best-matching positions, if they match at
least `need` of 25. Among equal scores the positions nearest (u, v) win. -/
def findAlign (m : Bits) (t : Homography) (u v r : Float) (scales : List Float) (need : Nat) :
    Option Pt := Id.run do
  let steps := (4 * r).toUInt64.toNat
  let mut best := 0
  let mut bestD := 1e30
  let mut sx := 0.0
  let mut sy := 0.0
  let mut cnt := 0.0
  for a in [0:2 * steps + 1] do
    for b in [0:2 * steps + 1] do
      let du := (a.toFloat - steps.toFloat) / 4
      let dv := (b.toFloat - steps.toFloat) / 4
      let d := du * du + dv * dv
      let sc := scales.foldl (fun acc s => max acc (alignScore m t (u + du) (v + dv) s)) 0
      if sc > best || (sc == best && d < bestD - 2) then
        best := sc
        bestD := d
        let p := t.apply (u + du) (v + dv)
        sx := p.x
        sy := p.y
        cnt := 1
      else if sc == best && (d - bestD).abs ≤ 2 then
        let p := t.apply (u + du) (v + dv)
        sx := sx + p.x
        sy := sy + p.y
        cnt := cnt + 1
  if best < need || cnt == 0 then return none
  return some ⟨sx / cnt, sy / cnt⟩

/-- The dark region (4-connected) containing `seed`, if it has at most
`cap` pixels. -/
def region (m : Bits) (sx sy cap : Nat) : Option (Array (Nat × Nat)) := Id.run do
  if !m.dark sx sy then return none
  let w := m.w
  let mut seen := ByteArray.mk (Array.replicate (w * m.h) 0)
  seen := bset seen (sy * w + sx) 1
  let mut stack : Array (Nat × Nat) := #[(sx, sy)]
  let mut out : Array (Nat × Nat) := #[]
  for _ in [0:cap + 1] do
    match stack.back? with
    | none => break
    | some (x, y) =>
      stack := stack.pop
      out := out.push (x, y)
      for (nx, ny) in [(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)] do
        let ok := !(nx == x - 1 && x == 0) && !(ny == y - 1 && y == 0)
        if ok && m.dark nx ny && bget seen (ny * w + nx) == 0 then
          seen := bset seen (ny * w + nx) 1
          stack := stack.push (nx, ny)
  return if stack.isEmpty then some out else none

/-- The four outer corners of the finder centred at `c` (module size
`ms`), by angle around it: the extreme points of its dark ring along the
diagonals (quirc's method), pushed half a pixel outwards. -/
def finderCorners (m : Bits) (c : Pt) (ms : Float) : Option (Array Pt) := do
  -- the ring: past the centre's dark run and the light ring
  let mut sx := 0
  let mut found := false
  let mut st := 0
  for k in [0:(6 * ms).toUInt64.toNat + 2] do
    if !found then
      let x := c.x + k.toFloat
      let d := m.darkAt x c.y
      if st == 0 && !d then st := 1
      else if st == 1 && d then
        sx := x.toUInt64.toNat
        found := true
  if !found then none
  let area := 24 * ms * ms
  let reg ← region m sx c.y.toUInt64.toNat (2 * area).toUInt64.toNat
  if reg.size.toFloat < area / 3 then none
  let pts := reg.map fun (x, y) => (Pt.mk (x.toFloat + 0.5) (y.toFloat + 0.5))
  let far := pts.foldl (fun (b : Pt) p => if p.d2 c > b.d2 c then p else b) c
  let ax := far.sub c
  let len := Float.sqrt (ax.x * ax.x + ax.y * ax.y)
  if len < 1 then none
  let ux := ax.x / len
  let uy := ax.y / len
  let along (p : Pt) := (p.x - c.x) * ux + (p.y - c.y) * uy
  let across (p : Pt) := -(p.x - c.x) * uy + (p.y - c.y) * ux
  let pick (f : Pt → Float) := pts.foldl (fun (b : Pt) p => if f p > f b then p else b) c
  let cs := #[far, pick across, pick (fun p => -along p), pick (fun p => -across p)]
  let out := cs.map fun p =>
    let d := p.dist c
    if d < 1 then p else p.add (Pt.scale (0.7 / d) (p.sub c))
  -- by angle (clockwise on screen, from the top-left)
  let ang (p : Pt) := Float.atan2 (p.y - c.y) (p.x - c.x)
  pure (out.qsort (fun a b => ang a < ang b))

/-- Module coordinates of the corners of the finders, by angle, with the
index of each finder's outer corner. -/
def finderModuleCorners (n : Nat) : Array (Array Pt × Nat) :=
  let e := n.toFloat
  #[(#[⟨0, 0⟩, ⟨7, 0⟩, ⟨7, 7⟩, ⟨0, 7⟩], 0),
    (#[⟨e - 7, 0⟩, ⟨e, 0⟩, ⟨e, 7⟩, ⟨e - 7, 7⟩], 1),
    (#[⟨0, e - 7⟩, ⟨7, e - 7⟩, ⟨7, e⟩, ⟨0, e⟩], 3)]

/-- Three finders taken as a symbol's: centres (top-left, top-right,
bottom-left), the module size between them, and each one's corners if
they were found. -/
structure Tri where
  tl : Pt
  tr : Pt
  bl : Pt
  ms : Float
  corners : Option (Array (Array Pt))

def Tri.of (m : Bits) (tl tr bl : Finder) : Tri :=
  let ms := ((sizeBetween m tl.c tr.c).getD tl.size + (sizeBetween m tl.c bl.c).getD tl.size) / 2
  let cs := [tl, tr, bl].mapM fun f => finderCorners m f.c ms
  { tl := tl.c, tr := tr.c, bl := bl.c, ms, corners := cs.map List.toArray }

/-- The first map of a symbol of size `n`: a homography through the
finder centres and their corners, or, without corners, the affine map
through the centres. -/
def finderMap (q : Tri) (n : Nat) : Option Homography := Id.run do
  let some cornerss := q.corners | return affineFor q.tl q.tr q.bl n
  let e := n.toFloat - 3.5
  let mut src : Array Pt := #[⟨3.5, 3.5⟩, ⟨e, 3.5⟩, ⟨3.5, e⟩]
  let mut dst : Array Pt := #[q.tl, q.tr, q.bl]
  let mid : Pt := ⟨(q.tr.x + q.bl.x) / 2, (q.tr.y + q.bl.y) / 2⟩
  let fs := #[q.tl, q.tr, q.bl]
  let mc := finderModuleCorners n
  for i in [0:3] do
    let c := fs[i]?.getD default
    let (mods, outer) := mc[i]?.getD (#[], 0)
    let cs := cornerss[i]?.getD #[]
    -- the corner farthest from the symbol's centre is the outer one
    let mut k := 0
    for j in [0:4] do
      if (cs[j]?.getD c).d2 mid > (cs[k]?.getD c).d2 mid then k := j
    for j in [0:4] do
      src := src.push (mods[j]?.getD default)
      dst := dst.push (cs[(k + 4 - outer + j) % 4]?.getD c)
  return (fitHomography src dst).orElse fun _ => affineFor q.tl q.tr q.bl n

/-- How well the timing patterns sampled through `t` alternate (out of
their length): the gate before the costlier work. -/
def timingAt (m : Bits) (t : Homography) (n : Nat) : Float := Id.run do
  if n < 21 then return 0
  let mut ok := 0
  for i in [8:n - 8] do
    let a := t.apply (i.toFloat + 0.5) 6.5
    let b := t.apply 6.5 (i.toFloat + 0.5)
    if m.darkAt a.x a.y == (i % 2 == 0) then ok := ok + 1
    if m.darkAt b.x b.y == (i % 2 == 0) then ok := ok + 1
  return ok.toFloat / (2 * (n - 16)).toFloat

/-- The module map of a symbol of size `n`: from the finders, then
refined through the alignment patterns found near where it predicts them.
`none` if the timing patterns do not show through the first map. -/
def mapFor (m : Bits) (q : Tri) (n : Nat) : Option Homography := do
  let t0 ← finderMap q n
  if timingAt m t0 n < 0.7 then none
  let v := (n - 17) / 4
  let ps := alignPos v
  if ps.length == 0 then return t0
  let e := n.toFloat - 3.5
  let mut src : Array Pt := #[⟨3.5, 3.5⟩, ⟨e, 3.5⟩, ⟨3.5, e⟩]
  let mut dst : Array Pt := #[q.tl, q.tr, q.bl]
  let mut t := t0
  -- the bottom-right alignment pattern, in growing windows
  let br := (ps.getLast?.getD 6).toFloat + 0.5
  let mut gotBr := false
  for (r, scales) in [(3.0, [0.8, 1.0, 1.25]), (8.0, [1.0])] do
    if !gotBr then
      if let some p := findAlign m t0 br br r scales 23 then
        src := src.push ⟨br, br⟩
        dst := dst.push p
        gotBr := true
  if gotBr then
    if let some h := fitHomography src dst then t := h
  -- every other alignment pattern, nearest the finders first
  let last := ps.length - 1
  let mut todo : Array (Float × Float × Float) := #[]
  for i in [0:ps.length] do
    for j in [0:ps.length] do
      let corner := (i == 0 && j == 0) || (i == 0 && j == last) || (i == last && j == 0) ||
        (i == last && j == last && gotBr)
      if !corner then
        let u := (ps.getD i 0).toFloat + 0.5
        let w := (ps.getD j 0).toFloat + 0.5
        let d := min ((u - 3.5) ^ 2 + (w - 3.5) ^ 2)
          (min ((u - e) ^ 2 + (w - 3.5) ^ 2) ((u - 3.5) ^ 2 + (w - e) ^ 2))
        todo := todo.push (d, u, w)
  for (_, u, w) in todo.qsort (fun a b => a.1 < b.1) do
    if let some p := findAlign m t u w 2 [1.0] 22 then
      src := src.push ⟨u, w⟩
      dst := dst.push p
      if src.size ≥ 4 then
        if let some h := fitHomography src dst then t := h
  return t

/-- The matrix sampled through `t`: each module the majority of nine
points around its centre. -/
def sampleGrid (m : Bits) (t : Homography) (n : Nat) : Grid := Id.run do
  let mut g := Grid.blank n
  for y in [0:n] do
    for x in [0:n] do
      let mut c := 0
      for j in [0:3] do
        for i in [0:3] do
          let p := t.apply (x.toFloat + 0.3 + 0.2 * i.toFloat) (y.toFloat + 0.3 + 0.2 * j.toFloat)
          if m.darkAt p.x p.y then c := c + 1
      if c ≥ 5 then g := g.set x y true
  return g

/-- How well the timing patterns alternate (out of their length). -/
def timingScore (g : Grid) : Float := Id.run do
  let n := g.n
  if n < 21 then return 0
  let mut ok := 0
  for i in [8:n - 8] do
    if g.get i 6 == (i % 2 == 0) then ok := ok + 1
    if g.get 6 i == (i % 2 == 0) then ok := ok + 1
  return ok.toFloat / (2 * (n - 16)).toFloat

/-- Samples and decodes a symbol of size `n`, or, when its version
information gives another size, of that size. -/
def tryAt (m : Bits) (q : Tri) (n : Nat) : Option Decoded := do
  let t ← mapFor m q n
  let g := sampleGrid m t n
  let v := (n - 17) / 4
  let v' := if v < 7 then none else (readVersion g).orElse fun _ => readVersion g.transpose
  match v' with
  | some v' =>
    if v' == v then decodeGridAny g
    else
      let n' := sizeOf v'
      let t ← mapFor m q n'
      decodeGridAny (sampleGrid m t n')
  | none => decodeGridAny g

/-- Decodes the symbol in a binarized frame. -/
def decodeBits (m : Bits) : Option Decoded := Id.run do
  let fs := findFinders m
  if fs.size < 3 then return none
  for (tl, tr, bl) in triangles fs do
    let q := Tri.of m tl tr bl
    for n in sizeCandidates q.tl q.tr q.bl q.ms do
      if let some d := tryAt m q n then return some d
  return none

/-- Decodes the QR symbol in a grayscale frame (`w × h` pixels, row
`stride` bytes apart). -/
def decodeImage (img : Image) : Option Decoded :=
  if !img.wellFormed then none
  else (decodeBits (hybridBits img)).orElse fun _ => decodeBits (globalBits img)

/-- The payload of the QR symbol in a grayscale frame, if one decodes. -/
def decode (w h : Nat) (px : ByteArray) (stride : Nat := w) : Option ByteArray :=
  (decodeImage { w, h, stride, px }).map (·.payload)

end Qr
