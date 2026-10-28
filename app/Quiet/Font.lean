/-
GNU Unifont, read from assets/font.bin (tools/font.py): every glyph of
the Basic Multilingual Plane and plane 1's emoji and symbols, smoothed by
Scale2x to 16 x 32 (narrow) or 32 x 32 (wide). The file is read once and
kept as one ByteArray; a glyph is located through the file's own table,
so nothing is decoded ahead of use.
-/
namespace Font

structure Font where
  bytes : ByteArray

def tableEnd : Nat := 4 + 4 * 0x20000

/-- The little-endian word at byte i. -/
@[inline] def Font.u32 (f : Font) (i : Nat) : UInt32 :=
  let b := f.bytes
  b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)

def load (path : String := "assets/font.bin") : IO Font := do
  let b ← IO.FS.readBinFile path
  if b.size < tableEnd || b.extract 0 4 != "QFNT".toUTF8 then
    throw (IO.userError s!"{path}: not a font")
  return ⟨b⟩

/-- A glyph: where its 32 rows start in the file, and whether it is wide. -/
structure Glyph where
  at_ : Nat
  wide : Bool

/-- The font's glyph for code point c, if it has one. -/
@[inline] def Font.glyph? (f : Font) (c : UInt32) : Option Glyph :=
  if c >= 0x20000 then none else
  let w := f.u32 (4 + 4 * c.toNat)
  if w == 0 then none
  else some ⟨tableEnd + ((w &&& 0x7FFFFFFF) - 1).toNat, w &&& 0x80000000 != 0⟩

/-- What a missing code point shows: the replacement character. -/
def Font.glyph (f : Font) (c : UInt32) : Glyph :=
  match f.glyph? c with
  | some g => g
  | none => (f.glyph? 0xFFFD).getD ⟨tableEnd, false⟩

/-- Row r (0..31) of a glyph, its leftmost pixel in bit 31. -/
@[inline] def Font.row (f : Font) (g : Glyph) (r : Nat) : UInt32 :=
  let b := f.bytes
  if g.wide then
    let i := g.at_ + 4 * r
    (b[i]!.toUInt32 <<< 24) ||| (b[i+1]!.toUInt32 <<< 16) ||| (b[i+2]!.toUInt32 <<< 8) ||| b[i+3]!.toUInt32
  else
    let i := g.at_ + 2 * r
    (b[i]!.toUInt32 <<< 24) ||| (b[i+1]!.toUInt32 <<< 16)

def Glyph.adv (g : Glyph) : Nat := if g.wide then 32 else 16

end Font
