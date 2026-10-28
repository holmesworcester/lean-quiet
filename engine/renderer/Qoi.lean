/-
A decoder for the QOI image format (qoiformat.org/qoi-specification.pdf).

The input is untrusted bytes. Every read is checked (`bytes[i]?`), so no
index can go out of bounds; the decoder refuses a bad magic, a width or
height outside 1..2048, an unknown channel count, and a stream that ends
before every pixel is made. Laws.lean states what a decoded image then
guarantees. Unlike the reference decoder, which keeps repeating the last
pixel when the stream runs dry, this one fails.

A pixel is packed as r << 24 | g << 16 | b << 8 | a.
-/
namespace Qoi

structure Qoi where
  w : UInt32
  h : UInt32
  px : Array UInt32

def max : UInt32 := 2048

/-! ## Pixels -/

@[inline] def Px.r (p : UInt32) : UInt32 := (p >>> 24) &&& 255
@[inline] def Px.g (p : UInt32) : UInt32 := (p >>> 16) &&& 255
@[inline] def Px.b (p : UInt32) : UInt32 := (p >>> 8) &&& 255
@[inline] def Px.a (p : UInt32) : UInt32 := p &&& 255

@[inline] def Px.pack (r g b a : UInt32) : UInt32 :=
  ((r &&& 255) <<< 24) ||| ((g &&& 255) <<< 16) ||| ((b &&& 255) <<< 8) ||| (a &&& 255)

@[inline] def Px.hash (p : UInt32) : UInt32 :=
  (Px.r p * 3 + Px.g p * 5 + Px.b p * 7 + Px.a p * 11) % 64

/-- A channel moved by d - bias, wrapping at 256. -/
@[inline] def Px.step (c d bias : UInt32) : UInt32 := (c + d + 256 - bias) &&& 255

/-! ## The stream -/

/-- The decoder's state: the last pixel, the index of recent pixels, how
many more times a run repeats the last pixel, and the next byte's
position. -/
structure St where
  px : UInt32
  ix : Array UInt32
  run : UInt32
  pos : Nat

/-- A pixel read from the stream: it goes into the index. -/
@[inline] def St.put (s : St) (p : UInt32) (pos : Nat) (run : UInt32) : UInt32 × St :=
  (p, ⟨p, s.ix.set! (Px.hash p).toNat p, run, pos⟩)

@[inline] def byte (bytes : ByteArray) (i : Nat) : Option UInt32 :=
  (bytes[i]?).map (·.toUInt32)

/-- The op at the state's position. -/
def St.read (bytes : ByteArray) (s : St) : Option (UInt32 × St) := do
  let p := s.px
  let i := s.pos
  let b1 ← byte bytes i
  if b1 == 254 then
    let r ← byte bytes (i + 1); let g ← byte bytes (i + 2); let b ← byte bytes (i + 3)
    return s.put (Px.pack r g b (Px.a p)) (i + 4) 0
  else if b1 == 255 then
    let r ← byte bytes (i + 1); let g ← byte bytes (i + 2); let b ← byte bytes (i + 3)
    let a ← byte bytes (i + 4)
    return s.put (Px.pack r g b a) (i + 5) 0
  else
    match b1 >>> 6 with
    | 0 => return s.put (s.ix[(b1 &&& 63).toNat]!) (i + 1) 0
    | 1 =>
      return s.put (Px.pack (Px.step (Px.r p) ((b1 >>> 4) &&& 3) 2)
        (Px.step (Px.g p) ((b1 >>> 2) &&& 3) 2) (Px.step (Px.b p) (b1 &&& 3) 2) (Px.a p)) (i + 1) 0
    | 2 =>
      let b2 ← byte bytes (i + 1)
      let vg := b1 &&& 63
      return s.put (Px.pack (Px.step (Px.r p) (vg + ((b2 >>> 4) &&& 15)) 40) (Px.step (Px.g p) vg 32)
        (Px.step (Px.b p) (vg + (b2 &&& 15)) 40) (Px.a p)) (i + 2) 0
    | _ => return s.put p (i + 1) (b1 &&& 63)

/-- The next pixel: a run repeats the last pixel; else an op is read. -/
@[inline] def St.next (bytes : ByteArray) (s : St) : Option (UInt32 × St) :=
  if s.run > 0 then some (s.px, { s with run := s.run - 1 }) else s.read bytes

/-- n more pixels onto acc: one pixel per step, so a success is exactly
n more. -/
def pixels (bytes : ByteArray) : Nat → St → Array UInt32 → Option (Array UInt32)
  | 0, _, acc => some acc
  | k + 1, s, acc =>
    match s.next bytes with
    | none => none
    | some (p, s') => pixels bytes k s' (acc.push p)

/-! ## The header -/

@[inline] def be (a b c d : UInt32) : UInt32 := (a <<< 24) ||| (b <<< 16) ||| (c <<< 8) ||| d

def body (w h : UInt32) (bytes : ByteArray) : Option Qoi :=
  let n := (w * h).toNat
  (pixels bytes n ⟨255, Array.replicate 64 0, 0, 14⟩ (Array.mkEmpty n)).map (⟨w, h, ·⟩)

def decode (bytes : ByteArray) : Option Qoi :=
  if bytes.size < 14 then none else
  let at_ i := bytes[i]!.toUInt32
  let w := be (at_ 4) (at_ 5) (at_ 6) (at_ 7)
  let h := be (at_ 8) (at_ 9) (at_ 10) (at_ 11)
  let ch := at_ 12
  if be (at_ 0) (at_ 1) (at_ 2) (at_ 3) == 1903126886 && 1 ≤ w && w ≤ max && 1 ≤ h && h ≤ max
      && (ch == 3 || ch == 4) then
    body w h bytes
  else none

end Qoi
