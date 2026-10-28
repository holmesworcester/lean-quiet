/-
GNU Unifont, read from assets/font.bin (tools/font.py): every glyph of
the Basic Multilingual Plane and plane 1's emoji and symbols, smoothed by
Scale2x (twice, for a 64-pixel cell): a narrow glyph is cell/2 pixels
wide, a wide one (CJK, emoji) cell pixels. The file is read once and
kept as one ByteArray; a glyph is located through the file's own table,
so nothing is decoded ahead of use.
-/
import Quiet.Emoji

namespace Font

structure Font where
  bytes : ByteArray
  /-- The cell's height in pixels (32, 48 or 64). -/
  cell : Nat
  /-- Colour emoji, drawn instead of Unifont's (Quiet/Emoji.lean). -/
  emoji : Emoji.Set

def tableEnd : Nat := 8 + 4 * 0x20000

/-- The little-endian word at byte i. -/
@[inline] def Font.u32 (f : Font) (i : Nat) : UInt32 :=
  let b := f.bytes
  b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)

def load (path : String := "assets/font.bin") : IO Font := do
  let b ← IO.FS.readBinFile path
  if b.size < tableEnd || b.extract 0 4 != "QFNT".toUTF8 then
    throw (IO.userError s!"{path}: not a font")
  let cell := (b[4]!.toNat ||| (b[5]!.toNat <<< 8))
  if cell != 32 && cell != 48 && cell != 64 then throw (IO.userError s!"{path}: cell {cell}")
  let emoji ← match ← (Emoji.load).toBaseIO with
    | .ok e => pure e
    | .error err => do IO.eprintln s!"no colour emoji: {err}"; pure default
  return ⟨b, cell, emoji⟩

/-- A glyph: where its 32 rows start in the file, and whether it is wide. -/
structure Glyph where
  at_ : Nat
  wide : Bool

/-- The font's glyph for code point c, if it has one. -/
@[inline] def Font.glyph? (f : Font) (c : UInt32) : Option Glyph :=
  if c >= 0x20000 then none else
  let w := f.u32 (8 + 4 * c.toNat)
  if w == 0 then none
  else some ⟨tableEnd + ((w &&& 0x7FFFFFFF) - 1).toNat, w &&& 0x80000000 != 0⟩

/-- What a missing code point shows: the replacement character. -/
def Font.glyph (f : Font) (c : UInt32) : Glyph :=
  match f.glyph? c with
  | some g => g
  | none => (f.glyph? 0xFFFD).getD ⟨tableEnd, false⟩

/-- Row r (0 .. cell - 1) of a glyph, its leftmost pixel in bit 63. -/
@[inline] def Font.row (f : Font) (g : Glyph) (r : Nat) : UInt64 := Id.run do
  let b := f.bytes
  let n := (if g.wide then f.cell else f.cell / 2) / 8
  let i := g.at_ + n * r
  let mut v : UInt64 := 0
  for k in [0:n] do
    v := v ||| (b[i + k]!.toUInt64 <<< (56 - 8 * k).toUInt64)
  return v

/-- A glyph's advance: half the cell, or the whole cell for a wide one. -/
def Font.adv (f : Font) (g : Glyph) : Nat := if g.wide then f.cell else f.cell / 2

end Font
