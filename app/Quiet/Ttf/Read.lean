/-
TrueType sfnt, metrics and quadratic glyf outlines. Simple and composite
glyphs (including point attachment and F2Dot14 transforms) share the
same checked reader. Recursion has depth and work fuel, and an ancestor
list rejects cycles. Instructions are skipped: rasterization is unhinted.
-/
import Quiet.Ttf.Cmap

namespace Ttf

structure Point where
  x : Float
  y : Float
  on : Bool
  deriving Inhabited

abbrev Contour := Array Point
abbrev Outline := Array Contour

structure Face where
  units : Nat
  ascender : Int
  descender : Int
  advances : Array Nat
  bearings : Array Int
  offsets : Array Nat
  glyf : ByteArray
  cmap : Cmap
  kern : Std.HashMap (Nat × Nat) Int := {}
  deriving Inhabited

def readKern (b : ByteArray) : Option (Std.HashMap (Nat × Nat) Int) := do
  if (← u16 b 0) != 0 then failure
  let n ← u16 b 2
  if n > 128 then failure
  let mut pos := 4
  let mut pairs := {}
  for _ in [0:n] do
    let len ← u16 b (pos + 2)
    if len < 6 then failure
    let sub ← slice b pos len
    let cov ← u16 sub 4
    if cov == 1 then
      let count ← u16 sub 6
      let _ ← slice sub 14 (6 * count)
      for j in [0:count] do
        let left ← u16 sub (14 + 6 * j)
        let right ← u16 sub (16 + 6 * j)
        let value ← i16 sub (18 + 6 * j)
        pairs := pairs.insert (left, right) value
    pos := pos + len
  return pairs

def readHeader (b : ByteArray) : Option Face := do
  if b.size > 32 * 1024 * 1024 || (← u32 b 0) != 0x00010000 then failure
  let head ← table b 0x68656164
  let hhea ← table b 0x68686561
  let maxp ← table b 0x6D617870
  let loca ← table b 0x6C6F6361
  let glyf ← table b 0x676C7966
  let hmtx ← table b 0x686D7478
  let cmap ← readCmap (← table b 0x636D6170)
  let _ ← slice head 0 54
  let _ ← slice hhea 0 36
  let _ ← slice maxp 0 32
  if (← u32 head 12) != 0x5F0F3CF5 || (← u32 maxp 0) != 0x00010000 then failure
  let units ← u16 head 18
  let format ← i16 head 50
  let count ← u16 maxp 4
  let metrics ← u16 hhea 34
  if units < 16 || units > 16384 || (format != 0 && format != 1) ||
      count == 0 || metrics == 0 || metrics > count then failure
  let mut offsets := #[]
  let mut previous := 0
  for i in [0:count + 1] do
    let off ← if format == 0 then (u16 loca (2 * i)).map (2 * ·) else u32 loca (4 * i)
    if off < previous || off > glyf.size then failure
    offsets := offsets.push off
    previous := off
  let mut advances := #[]
  let mut bearings := #[]
  for i in [0:count] do
    advances := advances.push (← u16 hmtx (4 * min i (metrics - 1)))
    bearings := bearings.push (← i16 hmtx (if i < metrics then 4 * i + 2 else 4 * metrics + 2 * (i - metrics)))
  for e in cmap do
    for c in [e.lo:e.hi + 1] do
      if e.glyph c ≥ count then failure
  let kern ← match table b 0x6B65726E with
    | none => pure {}
    | some k => readKern k
  return ⟨units, ← i16 hhea 4, ← i16 hhea 6, advances, bearings, offsets, glyf, cmap, kern⟩

/-- The actual hmtx advance, rounded to the nearest output pixel. -/
def advance (f : Face) (glyph size : Nat) : Nat :=
  ((f.advances[glyph]?.getD 0) * size + f.units / 2) / f.units

def kerning (f : Face) (left right size : Nat) : Int :=
  (f.kern[(left, right)]?.getD 0) * (size : Int) / (f.units : Int)

private def coord (b : ByteArray) (pos : Nat) (flag : Nat) (short same : Nat) : Option (Int × Nat) := do
  if flag &&& short != 0 then
    let n ← u8 b pos
    return (if flag &&& same != 0 then (n : Int) else -(n : Int), pos + 1)
  else if flag &&& same != 0 then return (0, pos)
  else return (← i16 b pos, pos + 2)

def simple (b : ByteArray) (contours : Nat) : Option Outline := do
  if contours > 1024 then failure
  let mut ends := #[]
  let mut prev := 0
  for i in [0:contours] do
    let e ← u16 b (10 + 2 * i)
    if i > 0 && e ≤ prev then failure
    ends := ends.push e
    prev := e
  let n := if contours == 0 then 0 else prev + 1
  if n > 8192 then failure
  let instructions ← u16 b (10 + 2 * contours)
  let mut pos := 12 + 2 * contours + instructions
  let _ ← slice b 0 pos
  let mut flags := #[]
  let mut repeats := 0
  let mut flag := 0
  for i in [0:n] do
    if repeats > 0 then repeats := repeats - 1
    else
      flag ← u8 b pos
      pos := pos + 1
      if flag &&& 8 != 0 then
        repeats ← u8 b pos
        pos := pos + 1
        if i + repeats ≥ n then failure
    flags := flags.push flag
  let mut xs := #[]
  let mut x := 0
  for fl in flags do
    let (dx, p) ← coord b pos fl 2 16
    pos := p
    x := x + dx
    xs := xs.push x
  let mut points := #[]
  let mut y := 0
  for i in [0:n] do
    let fl ← flags[i]?
    let (dy, p) ← coord b pos fl 4 32
    pos := p
    y := y + dy
    points := points.push ⟨(← xs[i]?).toFloat, y.toFloat, fl &&& 1 != 0⟩
  let mut out := #[]
  let mut start := 0
  for e in ends do
    out := out.push (points.extract start (e + 1))
    start := e + 1
  return out

private def pointAt (o : Outline) (i : Nat) : Option Point := o.flatten[i]?

/-- 32 levels, at most 4096 component visits, and 8192 output points.
A repeated ancestor is refused before following it. -/
def outlineGo : Nat → Face → Nat → List Nat → StateT Nat Option Outline
  | 0, _, _, _ => failure
  | depth + 1, f, glyph, ancestors => do
    let fuel ← get
    if fuel == 0 || ancestors.contains glyph then failure else do
      set (fuel - 1)
      let start ← f.offsets[glyph]?
      let stop ← f.offsets[glyph + 1]?
      if stop < start then failure else if stop == start then pure #[] else do
        let b ← slice f.glyf start (stop - start)
        let count ← i16 b 0
        let _ ← slice b 0 10
        if count ≥ 0 then simple b count.toNat else do
          if count != -1 then failure else do
            let mut out : Outline := #[]
            let mut pos := 10
            let mut more := true
            let mut lastFlags := 0
            for _ in [0:64] do
              if !more then break
              let flags ← u16 b pos
              let child ← u16 b (pos + 2)
              pos := pos + 4
              let words := flags &&& 1 != 0
              let xy := flags &&& 2 != 0
              let a ← if words then u16 b pos else u8 b pos
              let bArg ← if words then u16 b (pos + 2) else u8 b (pos + 1)
              pos := pos + (if words then 4 else 2)
              let mut xx : Float := 1
              let mut yy : Float := 1
              let mut xyM : Float := 0
              let mut yx : Float := 0
              if flags &&& 8 != 0 then
                xx := (← i16 b pos).toFloat / 16384
                yy := xx
                pos := pos + 2
              else if flags &&& 64 != 0 then
                xx := (← i16 b pos).toFloat / 16384
                yy := (← i16 b (pos + 2)).toFloat / 16384
                pos := pos + 4
              else if flags &&& 128 != 0 then
                xx := (← i16 b pos).toFloat / 16384
                xyM := (← i16 b (pos + 2)).toFloat / 16384
                yx := (← i16 b (pos + 4)).toFloat / 16384
                yy := (← i16 b (pos + 6)).toFloat / 16384
                pos := pos + 8
              let childOut ← outlineGo depth f child (glyph :: ancestors)
              let transformed := childOut.map (·.map fun p => { p with x := xx * p.x + yx * p.y, y := xyM * p.x + yy * p.y })
              let (dx, dy) ← if xy then do
                let ax := (signed a (if words then 16 else 8)).toFloat
                let ay := (signed bArg (if words then 16 else 8)).toFloat
                if flags &&& 0x1800 == 0x1800 then failure else
                  pure (if flags &&& 0x800 != 0 then (xx * ax + yx * ay, xyM * ax + yy * ay) else (ax, ay))
              else do
                let parentPoint ← pointAt out a
                let childPoint ← pointAt transformed bArg
                pure (parentPoint.x - childPoint.x, parentPoint.y - childPoint.y)
              let dx := if flags &&& 4 != 0 then dx.round else dx
              let dy := if flags &&& 4 != 0 then dy.round else dy
              out := out ++ transformed.map (·.map fun p => { p with x := p.x + dx, y := p.y + dy })
              if (out.foldl (fun (n : Nat) c => n + c.size) 0) > 8192 then failure
              more := flags &&& 32 != 0
              lastFlags := flags
            if more then failure else do
              if lastFlags &&& 256 != 0 then
                let len ← u16 b pos
                let _ ← slice b (pos + 2) len
                pure ()
              pure out

def outline (f : Face) (glyph : Nat) : Option Outline :=
  (outlineGo 32 f glyph [] 4096).map (·.1)

/-- A font is exposed only after every glyph has passed the bounded
outline reader, including glyphs the UI has not requested yet. -/
def read (b : ByteArray) : Option Face := do
  let f ← readHeader b
  for g in [0:f.advances.size] do
    let _ ← outline f g
  return f

end Ttf
