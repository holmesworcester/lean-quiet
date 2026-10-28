/-
The module matrix: function patterns, where codeword bits go, masks, and
format and version information. The encoder draws a symbol here; the
decoder reads a sampled matrix back with the same placement functions, so
both sides agree by construction on where every bit lives.

A matrix is `n × n` modules, row-major in a `ByteArray` (1 dark, 0 light);
`x` is the column and `y` the row. Reads are `a[i]?` with a default, and
writes outside the matrix are dropped.
-/
import Qr.Tables
import Qr.Format

namespace Qr

@[inline] def bget (a : ByteArray) (i : Nat) : UInt8 := a[i]?.getD 0

@[inline] def bset (a : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < a.size then a.set i v h else a

/-- A square matrix of modules. -/
structure Grid where
  n : Nat
  m : ByteArray

namespace Grid

def blank (n : Nat) : Grid := ⟨n, ByteArray.mk (Array.replicate (n * n) 0)⟩

@[inline] def get (g : Grid) (x y : Nat) : Bool := x < g.n && y < g.n && bget g.m (y * g.n + x) != 0

@[inline] def set (g : Grid) (x y : Nat) (b : Bool) : Grid :=
  if x < g.n ∧ y < g.n then { g with m := bset g.m (y * g.n + x) (if b then 1 else 0) } else g

/-- The matrix mirrored about its main diagonal. -/
def transpose (g : Grid) : Grid := Id.run do
  let mut t := blank g.n
  for y in [0:g.n] do
    for x in [0:g.n] do
      t := t.set y x (g.get x y)
  return t

def dark (g : Grid) : Nat := Id.run do
  let mut c := 0
  for i in [0:g.n * g.n] do
    if bget g.m i != 0 then c := c + 1
  return c

end Grid

/-- A matrix being drawn: modules and which of them are function patterns. -/
structure Canvas where
  mods : Grid
  fn : Grid

namespace Canvas

/-- Sets a function module (dropped outside the matrix). -/
@[inline] def put (c : Canvas) (x y : Nat) (b : Bool) : Canvas :=
  { mods := c.mods.set x y b, fn := c.fn.set x y true }

/-- The 9×9 finder (with its separator) centred at (cx, cy). -/
def finder (c : Canvas) (cx cy : Nat) : Canvas := Id.run do
  let mut c := c
  for i in [0:9] do
    for j in [0:9] do
      if cx + i ≥ 4 ∧ cy + j ≥ 4 then
        let d := max (if i ≥ 4 then i - 4 else 4 - i) (if j ≥ 4 then j - 4 else 4 - j)
        c := c.put (cx + i - 4) (cy + j - 4) (d != 2 && d != 4)
  return c

def align (c : Canvas) (cx cy : Nat) : Canvas := Id.run do
  let mut c := c
  for i in [0:5] do
    for j in [0:5] do
      let d := max (if i ≥ 2 then i - 2 else 2 - i) (if j ≥ 2 then j - 2 else 2 - j)
      c := c.put (cx + i - 2) (cy + j - 2) (d != 1)
  return c

end Canvas

/-- Where format bit `i` (bit 0 least significant) goes, in the copy
around the top-left finder and in the copy split between the other two. -/
def formatPos1 (i : Nat) : Nat × Nat :=
  if i < 6 then (8, i) else if i = 6 then (8, 7) else if i = 7 then (8, 8)
  else if i = 8 then (7, 8) else (14 - i, 8)

def formatPos2 (n i : Nat) : Nat × Nat :=
  if i < 8 then (n - 1 - i, 8) else (8, n - 15 + i)

/-- Where version bit `i` goes: the block by the top-right finder (the
block by the bottom-left one is its transpose). -/
def versionPos (n i : Nat) : Nat × Nat := (n - 11 + i % 3, i / 3)

def Canvas.formatBits (c : Canvas) (bits : Nat) : Canvas := Id.run do
  let n := c.mods.n
  let mut c := c
  for i in [0:15] do
    let b := bits.testBit i
    let (x, y) := formatPos1 i
    c := c.put x y b
    let (x, y) := formatPos2 n i
    c := c.put x y b
  c := c.put 8 (n - 8) true
  return c

def Canvas.versionBits (c : Canvas) (v : Nat) : Canvas := Id.run do
  if v < 7 then return c
  let n := c.mods.n
  let bits := bchVersion v
  let mut c := c
  for i in [0:18] do
    let (x, y) := versionPos n i
    c := c.put x y (bits.testBit i)
    c := c.put y x (bits.testBit i)
  return c

/-- The function patterns of a version: finders and separators, timing,
alignment patterns, format (blank) and version information. -/
def functionCanvas (v : Nat) : Canvas := Id.run do
  let n := sizeOf v
  let mut c : Canvas := ⟨Grid.blank n, Grid.blank n⟩
  for i in [0:n] do
    c := c.put 6 i (i % 2 == 0)
    c := c.put i 6 (i % 2 == 0)
  c := c.finder 3 3
  c := c.finder (n - 4) 3
  c := c.finder 3 (n - 4)
  let ps := alignPos v
  let last := ps.length - 1
  for i in [0:ps.length] do
    for j in [0:ps.length] do
      if !((i == 0 && j == 0) || (i == 0 && j == last) || (i == last && j == 0)) then
        c := c.align (ps.getD i 0) (ps.getD j 0)
  c := c.formatBits 0
  c := c.versionBits v
  return c

/-- Positions (`y * n + x`) of the data modules in placement order: the
zigzag of two-column strips from the right, up then down, skipping the
vertical timing column. -/
def dataPositions (n : Nat) (fn : Grid) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for k in [0:n / 2] do
    let r0 := n - 1 - 2 * k
    let right := if r0 ≤ 6 then r0 - 1 else r0
    let upward := (right + 1) &&& 2 == 0
    for vert in [0:n] do
      let y := if upward then n - 1 - vert else vert
      for j in [0:2] do
        let x := right - j
        if !fn.get x y then out := out.push (y * n + x)
  return out

/-- The mask condition: data module (x, y) is flipped where it holds. -/
def maskBit (k x y : Nat) : Bool :=
  match k with
  | 0 => (x + y) % 2 == 0
  | 1 => y % 2 == 0
  | 2 => x % 3 == 0
  | 3 => (x + y) % 3 == 0
  | 4 => (x / 3 + y / 2) % 2 == 0
  | 5 => x * y % 2 + x * y % 3 == 0
  | 6 => (x * y % 2 + x * y % 3) % 2 == 0
  | _ => ((x + y) % 2 + x * y % 3) % 2 == 0

/-! ## Mask penalty (ISO/IEC 18004 §7.8.3) -/

/-- Finder-like runs in a line's run history (newest first): dark-light-
dark(3)-light-dark at 1:1:3:1:1 with four light modules on one side. -/
def finderLike (h : Array Nat) : Nat :=
  let g (i : Nat) := h[i]?.getD 0
  let n := g 1
  let core := n > 0 && g 2 == n && g 3 == n * 3 && g 4 == n && g 5 == n
  (if core && g 0 ≥ n * 4 && g 6 ≥ n then 1 else 0) +
  (if core && g 6 ≥ n * 4 && g 0 ≥ n then 1 else 0)

/-- The run history after a run of `len` (the quiet zone counts as light
before the first run). -/
def pushRun (n : Nat) (h : Array Nat) (len : Nat) : Array Nat :=
  let len := if h[0]?.getD 0 == 0 then len + n else len
  (#[len] ++ h).extract 0 7

/-- Penalty of one line: N1 runs of five or more, N3 finder-like
patterns. `get i` is the line's i-th module. -/
def linePenalty (n : Nat) (get : Nat → Bool) : Nat := Id.run do
  let mut score := 0
  let mut color := false
  let mut run := 0
  let mut h : Array Nat := Array.replicate 7 0
  for i in [0:n] do
    let c := get i
    if c == color then
      run := run + 1
      if run == 5 then score := score + 3
      else if run > 5 then score := score + 1
    else
      h := pushRun n h run
      if !color then score := score + finderLike h * 40
      color := c
      run := 1
  -- end of the line: close the run, then the quiet zone's light run
  if color then
    h := pushRun n h run
    run := 0
  h := pushRun n h (run + n)
  score := score + finderLike h * 40
  return score

def penalty (g : Grid) : Nat := Id.run do
  let n := g.n
  let mut s := 0
  for y in [0:n] do
    s := s + linePenalty n (fun x => g.get x y)
  for x in [0:n] do
    s := s + linePenalty n (fun y => g.get x y)
  for y in [0:n - 1] do
    for x in [0:n - 1] do
      let c := g.get x y
      if c == g.get (x + 1) y && c == g.get x (y + 1) && c == g.get (x + 1) (y + 1) then
        s := s + 3
  let total := n * n
  let dark := g.dark
  let dev := if dark * 20 ≥ total * 10 then dark * 20 - total * 10 else total * 10 - dark * 20
  let k := (dev + total - 1) / total - 1
  return s + k * 10

end Qr
