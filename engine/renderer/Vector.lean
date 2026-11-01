/-
Filled vector outlines at their final device size, for the brand lockup
(`ui/brand`), whose pinned source is SVG path data. Only absolute
M/L/H/V/C/Z are read, which is all that source uses; any other command is
refused (`parse` is `none`), never guessed.

Cubics are flattened to at most 1/256 pixel deviation from the curve
(Wang's bound). The outline is then filled by nonzero or even-odd
winding on the 8 × 8 sample grid of `Ttf.rasterRaw`, with its coverage
law (`Ttf.coverage`). A span adds its samples to each pixel it crosses
instead of one sample at a time, and each subrow visits only the edges
that span it (`active`), so a lockup costs about its own pixel count.
-/
import engine.renderer.Ttf.Raster

namespace Vector

inductive Rule where
  | nonzero | evenOdd
  deriving BEq, Inhabited, Repr

structure Pt where
  x : Float
  y : Float
  deriving Inhabited

inductive Seg where
  | line (to : Pt)
  | cubic (c1 c2 to : Pt)
  deriving Inhabited

structure Contour where
  start : Pt
  segs : Array Seg
  deriving Inhabited

/-- One filled `<path>`: its rule and its closed contours. -/
structure Path where
  rule : Rule
  contours : Array Contour
  deriving Inhabited

/-! ## Path data -/

inductive Tok where
  | cmd (c : Char)
  | num (v : Float)
  deriving Inhabited

private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- An SVG number: sign, digits, and at most one '.', so "1.5.5" is two
numbers and "1-2" is two numbers, as SVG reads them. No exponents (the
source has none); a letter 'e' is refused by `tokens`. -/
private def number (cs : List Char) : Option (Float × List Char) := Id.run do
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let intPart := cs.takeWhile digit
  let cs := cs.drop intPart.length
  let (frac, cs) := match cs with
    | '.' :: r => let f := r.takeWhile digit; (f, r.drop f.length)
    | r => ([], r)
  if intPart.isEmpty && frac.isEmpty then return none
  let mantissa := (intPart ++ frac).foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0
  let v := Float.ofScientific mantissa true frac.length
  return some (if neg then -v else v, cs)

/-- Commands and numbers; separators are spaces, commas and newlines. -/
def tokens (d : String) : Option (Array Tok) := go d.toList #[] (d.length + 1)
where
  go : List Char → Array Tok → Nat → Option (Array Tok)
    | _, _, 0 => none
    | [], acc, _ => some acc
    | c :: r, acc, fuel + 1 =>
      if c == ' ' || c == ',' || c == '\n' || c == '\t' || c == '\r' then go r acc fuel
      else if "MLHVCZ".contains c then go r (acc.push (.cmd c)) fuel
      else match number (c :: r) with
        | some (v, rest) => if rest.length < r.length + 1 then go rest (acc.push (.num v)) fuel else none
        | none => none

/-- Contours from path data. A command's arguments may repeat (a second
pair after M is a line, as in SVG). Every contour is closed by Z or by
the next M; an open contour is filled as if closed, as SVG fills it. -/
def parse (d : String) : Option (Array Contour) := do
  let ts ← tokens d
  let mut out : Array Contour := #[]
  let mut cur : Option Contour := none
  let mut pen : Pt := ⟨0, 0⟩
  let mut cmd : Char := ' '
  let mut i := 0
  let mut nums : Array Float := #[]
  -- Gather each command's numbers, then apply them in groups.
  let mut groups : Array (Char × Array Float) := #[]
  for t in ts do
    match t with
    | .cmd c =>
      if cmd != ' ' then groups := groups.push (cmd, nums)
      cmd := c; nums := #[]
    | .num v => if cmd == ' ' then failure else nums := nums.push v
  if cmd != ' ' then groups := groups.push (cmd, nums)
  for (c, ns) in groups do
    let arity := match c with | 'M' | 'L' => 2 | 'H' | 'V' => 1 | 'C' => 6 | _ => 0
    if arity == 0 then
      if !ns.isEmpty then failure
      if let some k := cur then out := out.push k; pen := k.start
      cur := none
      continue
    if ns.isEmpty || ns.size % arity != 0 then failure
    i := 0
    while i < ns.size do
      let a (k : Nat) := ns[i + k]!
      match c with
      | 'M' =>
        if i == 0 then
          if let some k := cur then out := out.push k
          pen := ⟨a 0, a 1⟩
          cur := some ⟨pen, #[]⟩
        else
          pen := ⟨a 0, a 1⟩
          cur := cur.map fun k => { k with segs := k.segs.push (.line pen) }
      | 'L' => pen := ⟨a 0, a 1⟩; cur := cur.map fun k => { k with segs := k.segs.push (.line pen) }
      | 'H' => pen := { pen with x := a 0 }; cur := cur.map fun k => { k with segs := k.segs.push (.line pen) }
      | 'V' => pen := { pen with y := a 0 }; cur := cur.map fun k => { k with segs := k.segs.push (.line pen) }
      | _ =>
        let to : Pt := ⟨a 4, a 5⟩
        cur := cur.map fun k => { k with segs := k.segs.push (.cubic ⟨a 0, a 1⟩ ⟨a 2, a 3⟩ to) }
        pen := to
      if cur.isNone then failure
      i := i + arity
  if let some k := cur then out := out.push k
  return out

/-! ## Flattening -/

/-- A transform to device pixels: scale, then offset. -/
structure Place where
  scale : Float
  dx : Float
  dy : Float
  deriving Inhabited

def Place.at (p : Place) (q : Pt) : Pt := ⟨p.dx + p.scale * q.x, p.dy + p.scale * q.y⟩

/-- Pieces a cubic needs for ≤ 1/256 px deviation: Wang's bound,
n = ⌈√(3·2/8 · M / tol)⌉ with M the larger second difference, capped. -/
def pieces (a b c d : Pt) : Nat :=
  let ddx1 := a.x - 2 * b.x + c.x
  let ddy1 := a.y - 2 * b.y + c.y
  let ddx2 := b.x - 2 * c.x + d.x
  let ddy2 := b.y - 2 * c.y + d.y
  let m := max (ddx1 * ddx1 + ddy1 * ddy1).sqrt (ddx2 * ddx2 + ddy2 * ddy2).sqrt
  let n := (0.75 * m * 256).sqrt.ceil
  if n.isFinite then max 1 (min 256 n.toUInt64.toNat) else 1

/-- The outline's edges in device pixels. -/
def edges (p : Place) (cs : Array Contour) : Array Ttf.Edge := Id.run do
  let mut out := #[]
  for k in cs do
    let first := p.at k.start
    let mut prev := first
    for s in k.segs do
      match s with
      | .line to =>
        let q := p.at to
        out := out.push ⟨prev.x, prev.y, q.x, q.y⟩
        prev := q
      | .cubic c1 c2 to =>
        let (b, c, d) := (p.at c1, p.at c2, p.at to)
        let n := pieces prev b c d
        let a := prev
        for i in [1:n + 1] do
          let t := i.toFloat / n.toFloat
          let u := 1 - t
          let q : Pt := ⟨u*u*u*a.x + 3*u*u*t*b.x + 3*u*t*t*c.x + t*t*t*d.x,
                         u*u*u*a.y + 3*u*u*t*b.y + 3*u*t*t*c.y + t*t*t*d.y⟩
          out := out.push ⟨prev.x, prev.y, q.x, q.y⟩
          prev := q
    out := out.push ⟨prev.x, prev.y, first.x, first.y⟩
  return out

/-! ## Filling -/

/-- A coverage mask: w × h bytes at (x, y) in device pixels. -/
structure Mask where
  x : Int
  y : Int
  w : Nat
  h : Nat
  pixels : ByteArray
  deriving Inhabited

def Mask.Valid (m : Mask) : Prop := m.pixels.size = m.w * m.h

private def floorInt (x : Float) : Int := x.floor.toInt64.toInt
private def ceilInt (x : Float) : Int := x.ceil.toInt64.toInt

/-- Whether a winding count is inside, by the rule. -/
def Rule.inside : Rule → Int → Bool
  | .nonzero, w => w != 0
  | .evenOdd, w => w % 2 != 0

/-- Add samples [a, z) of a subrow to the pixels they fall in (8 a pixel). -/
def addSpan (row : Array Nat) (a z : Nat) : Array Nat := Id.run do
  if z ≤ a then return row
  let p0 := a / 8
  let p1 := (z - 1) / 8
  if p0 == p1 then return row.modify p0 (· + (z - a))
  let mut row := row.modify p0 (· + (8 * (p0 + 1) - a))
  for p in [p0 + 1:p1] do row := row.modify p (· + 8)
  return row.modify p1 (· + (z - 8 * p1))

/-- Fill paths (each by its own rule) into one mask, clipped to a box of
at most 4096 × 4096. Samples are at ((k + .5)/8) in both axes, as in
`Ttf.rasterRaw`; a pixel's coverage is `Ttf.coverage` of its samples. -/
def fill (paths : Array (Rule × Array Ttf.Edge)) : Mask := Id.run do
  let all := paths.foldl (fun acc (_, es) => acc ++ es) #[]
  let some e0 := all[0]? | return ⟨0, 0, 0, 0, .empty⟩
  let mut xmin := min e0.x0 e0.x1
  let mut xmax := max e0.x0 e0.x1
  let mut ymin := min e0.y0 e0.y1
  let mut ymax := max e0.y0 e0.y1
  for e in all do
    if !(e.x0.isFinite && e.x1.isFinite && e.y0.isFinite && e.y1.isFinite) then return ⟨0, 0, 0, 0, .empty⟩
    xmin := min xmin (min e.x0 e.x1); xmax := max xmax (max e.x0 e.x1)
    ymin := min ymin (min e.y0 e.y1); ymax := max ymax (max e.y0 e.y1)
  let x0 := floorInt xmin
  let y0 := floorInt ymin
  let w := (ceilInt xmax - x0).toNat
  let h := (ceilInt ymax - y0).toNat
  if w == 0 || h == 0 || w > 4096 || h > 4096 then return ⟨x0, y0, 0, 0, .empty⟩
  -- Each path keeps its non-horizontal edges, sorted by their top.
  let sorted := paths.map fun (rule, es) =>
    (rule, (es.filter fun (e : Ttf.Edge) => e.y0 != e.y1).qsort (fun (a b : Ttf.Edge) => min a.y0 a.y1 < min b.y0 b.y1))
  let mut next := sorted.map fun _ => 0
  let mut active : Array (Array Ttf.Edge) := sorted.map fun _ => #[]
  let mut counts : Array Nat := Array.replicate (w * h) 0
  for r in [0:h] do
    let mut row : Array Nat := Array.replicate w 0
    for sy in [0:8] do
      let y := y0.toFloat + r.toFloat + (sy.toFloat + 0.5) / 8
      for pi in [0:sorted.size] do
        let (rule, es) := sorted[pi]!
        let mut act := active[pi]!.filter fun (e : Ttf.Edge) => y < max e.y0 e.y1
        let mut k := next[pi]!
        while h : k < es.size do
          let e := es[k]
          if min e.y0 e.y1 ≤ y then
            if y < max e.y0 e.y1 then act := act.push e
            k := k + 1
          else break
        next := next.set! pi k
        active := active.set! pi act
        let mut crossings : Array (Float × Int) := #[]
        for e in act do
          if (e.y0 ≤ y && y < e.y1) || (e.y1 ≤ y && y < e.y0) then
            crossings := crossings.push (e.x0 + (y - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0), if e.y1 > e.y0 then 1 else -1)
        crossings := crossings.qsort (fun a b => a.1 < b.1)
        let mut winding : Int := 0
        let mut left : Float := 0
        for (x, direction) in crossings do
          if rule.inside winding then
            let a := (max 0 (ceilInt ((left - x0.toFloat) * 8 - 0.5))).toNat
            let z := min (w * 8) (max 0 (ceilInt ((x - x0.toFloat) * 8 - 0.5))).toNat
            row := addSpan row a z
          winding := winding + direction
          left := x
    for x in [0:w] do
      counts := counts.set! (r * w + x) (min 64 row[x]!)
  let pixels := counts.foldl (fun b n => b.push (Ttf.coverage n)) (ByteArray.emptyWithCapacity (w * h))
  return ⟨x0, y0, w, h, pixels⟩

end Vector
