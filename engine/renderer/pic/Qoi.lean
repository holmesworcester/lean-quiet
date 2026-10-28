/-
QOI (qoiformat.org/qoi-specification.pdf): how the composer stores a
picture. Lean-quiet keeps pictures as QOI blobs; this is the encoder and a
decoder for them.

The encoder keeps its index of recent pixels exactly as every QOI decoder
does (each pixel, runs included, is put at its hash), so the index ops it
writes decode the same in any decoder. The decoder reads untrusted bytes
through `b[i]?` only, refuses a bad magic, a side outside 1..2048 or an
unknown channel count, and fails when the stream ends early (the reference
decoder repeats the last pixel instead). It is structural recursion on the
pixels left, so it ends on every input.

A picture is RGBA, 4 bytes a pixel, row-major: what the native side hands
over (an Android `Bitmap`'s ARGB_8888 bytes are R, G, B, A).
-/
namespace Pic

/-- An RGBA picture, 4 bytes a pixel, row-major. -/
structure Rgba where
  w : Nat
  h : Nat
  px : ByteArray

def Rgba.wellFormed (p : Rgba) : Bool := p.px.size == 4 * p.w * p.h

/-- The largest side a stored picture may have. -/
def maxSide : Nat := 2048

structure Px where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
  deriving DecidableEq, Inhabited

def Px.hash (p : Px) : Nat := (p.r.toNat * 3 + p.g.toNat * 5 + p.b.toNat * 7 + p.a.toNat * 11) % 64

/-- The pixel QOI starts from. -/
def Px.start : Px := ⟨0, 0, 0, 255⟩

@[inline] def get8 (b : ByteArray) (i : Nat) : UInt8 := b[i]?.getD 0

/-- Writes a byte; a write outside the array is dropped. -/
@[inline] def put8 (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < b.size then b.set i v h else b

@[inline] def Rgba.at (p : Rgba) (i : Nat) : Px :=
  ⟨get8 p.px (4 * i), get8 p.px (4 * i + 1), get8 p.px (4 * i + 2), get8 p.px (4 * i + 3)⟩

/-! ## Encoding -/

/-- One op's bytes for pixel `p` after `prev`, with the index `ix` (not a
run): an index hit, a small difference, a luma difference, RGB, or RGBA. -/
def opBytes (ix : Array Px) (prev p : Px) (out : ByteArray) : ByteArray :=
  let h := p.hash
  if ix[h]? == some p then out.push h.toUInt8
  else if p.a != prev.a then out.push 255 |>.push p.r |>.push p.g |>.push p.b |>.push p.a
  else
    -- differences, wrapping at 256, biased into unsigned fields
    let dr := p.r - prev.r
    let dg := p.g - prev.g
    let db := p.b - prev.b
    if dr + 2 < 4 && dg + 2 < 4 && db + 2 < 4 then
      out.push ((0x40 : UInt8) ||| ((dr + 2) <<< 4) ||| ((dg + 2) <<< 2) ||| (db + 2))
    else if dg + 32 < 64 && dr - dg + 8 < 16 && db - dg + 8 < 16 then
      out.push ((0x80 : UInt8) ||| (dg + 32)) |>.push (((dr - dg + 8) <<< 4) ||| (db - dg + 8))
    else out.push 254 |>.push p.r |>.push p.g |>.push p.b

structure Enc where
  prev : Px
  ix : Array Px
  run : Nat
  out : ByteArray

@[inline] def Enc.flush (s : Enc) : Enc :=
  if s.run == 0 then s else { s with run := 0, out := s.out.push ((0xC0 : UInt8) ||| (s.run - 1).toUInt8) }

/-- One more pixel: a repeat of the last extends the run (at most 62); any
other ends it and writes its own op. Either way the index learns it. -/
def Enc.step (s : Enc) (p : Px) : Enc :=
  let s :=
    if p == s.prev then
      let s := { s with run := s.run + 1 }
      if s.run == 62 then s.flush else s
    else
      let s := s.flush
      { s with out := opBytes s.ix s.prev p s.out }
  { s with prev := p, ix := s.ix.setIfInBounds p.hash p }

def be32 (out : ByteArray) (v : Nat) : ByteArray :=
  out.push (v / 16777216 % 256).toUInt8 |>.push (v / 65536 % 256).toUInt8
    |>.push (v / 256 % 256).toUInt8 |>.push (v % 256).toUInt8

/-- The picture as QOI: header (4 channels, sRGB), ops, end marker. -/
def encode (p : Rgba) : ByteArray := Id.run do
  let head := be32 (be32 ("qoif".toUTF8) p.w) p.h |>.push 4 |>.push 0
  let mut s : Enc := ⟨.start, Array.replicate 64 ⟨0, 0, 0, 0⟩, 0, head⟩
  for i in [0:p.w * p.h] do
    s := s.step (p.at i)
  s := s.flush
  return s.out ++ ⟨#[0, 0, 0, 0, 0, 0, 0, 1]⟩

/-! ## Decoding -/

structure Dec where
  prev : Px
  ix : Array Px
  /-- repeats of `prev` still owed by a run -/
  run : Nat
  pos : Nat

/-- The pixel the op at `s.pos` makes, and the position after it. -/
def Dec.op (b : ByteArray) (s : Dec) : Option (Px × Nat × Nat) := do
  let i := s.pos
  let p := s.prev
  let b1 ← b[i]?
  if b1 == 254 then
    let r ← b[i + 1]?; let g ← b[i + 2]?; let bl ← b[i + 3]?
    pure (⟨r, g, bl, p.a⟩, i + 4, 0)
  else if b1 == 255 then
    let r ← b[i + 1]?; let g ← b[i + 2]?; let bl ← b[i + 3]?; let a ← b[i + 4]?
    pure (⟨r, g, bl, a⟩, i + 5, 0)
  else match b1 >>> 6 with
    | 0 => pure ((s.ix[(b1 &&& 63).toNat]?).getD default, i + 1, 0)
    | 1 =>
      pure (⟨p.r + ((b1 >>> 4) &&& 3) - 2, p.g + ((b1 >>> 2) &&& 3) - 2, p.b + (b1 &&& 3) - 2, p.a⟩,
        i + 1, 0)
    | 2 =>
      let b2 ← b[i + 1]?
      let vg := (b1 &&& 63) - 32
      pure (⟨p.r + vg + ((b2 >>> 4) &&& 15) - 8, p.g + vg, p.b + vg + (b2 &&& 15) - 8, p.a⟩, i + 2, 0)
    | _ => pure (p, i + 1, (b1 &&& 63).toNat)

/-- The next pixel: one owed by a run, or an op's. The index learns it. -/
def Dec.next (b : ByteArray) (s : Dec) : Option (Px × Dec) := do
  let (p, pos, run) ← if s.run > 0 then pure (s.prev, s.pos, s.run - 1) else s.op b
  pure (p, { prev := p, ix := s.ix.setIfInBounds p.hash p, run, pos })

/-- `n` more pixels onto `acc`. -/
def pixels (b : ByteArray) : Nat → Dec → ByteArray → Option ByteArray
  | 0, _, acc => some acc
  | n + 1, s, acc =>
    match s.next b with
    | none => none
    | some (p, s') => pixels b n s' (acc.push p.r |>.push p.g |>.push p.b |>.push p.a)

def rd32 (b : ByteArray) (i : Nat) : Nat :=
  (get8 b i).toNat * 16777216 + (get8 b (i + 1)).toNat * 65536 + (get8 b (i + 2)).toNat * 256 +
    (get8 b (i + 3)).toNat

/-- A QOI blob's picture, as RGBA. -/
def decode (b : ByteArray) : Option Rgba :=
  let w := rd32 b 4
  let h := rd32 b 8
  if b.size < 14 || rd32 b 0 != 0x716f6966 || w < 1 || h < 1 || w > maxSide || h > maxSide ||
      (get8 b 12 != 3 && get8 b 12 != 4) then none
  else
    (pixels b (w * h) { prev := .start, ix := Array.replicate 64 ⟨0, 0, 0, 0⟩, run := 0, pos := 14 }
      (ByteArray.emptyWithCapacity (4 * w * h))).map fun px => { w, h, px }

end Pic
