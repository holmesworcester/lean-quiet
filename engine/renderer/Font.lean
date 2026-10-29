/-
Noto TrueType metrics and cached Lean coverage bitmaps, with GNU Unifont
and colour emoji fallback. The cell is in screen pixels (density scaled
from the asset's 420-dpi cell); the bitmap fallback is resampled from its
source cell. Noto and the TrueType reader live in their own modules.
-/
import engine.renderer.Emoji
import engine.renderer.Noto
import engine.renderer.Glyphs

namespace Font

structure Font where
  bytes : ByteArray
  /-- The cell's height in screen pixels (16..64). -/
  cell : Nat
  /-- Colour emoji, drawn instead of Unifont's (Quiet/Emoji.lean). -/
  emoji : Emoji.Set
  noto : Noto.Set := {}
  sourceCell : Nat := 48
  sizes : Std.HashMap Nat Noto.Set := {}
  icons : Glyphs.Set := {}
  /-- Layout-only high precision metrics; never used to paint a glyph. -/
  fineMetrics : Bool := false

def tableEnd : Nat := 8 + 4 * 0x20000

/-- The little-endian word at byte i. -/
@[inline] def Font.u32 (f : Font) (i : Nat) : UInt32 :=
  let b := f.bytes
  b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)

def pixelCell (source density : Nat) : Nat := max 16 (min 64 ((source * density + 210) / 420))

def load (path : String := "assets/font.bin") (density : Nat := 420) : IO Font := do
  let b ← IO.FS.readBinFile path
  if b.size < tableEnd || b.extract 0 4 != "QFNT".toUTF8 then
    throw (IO.userError s!"{path}: not a font")
  let cell := (b[4]!.toNat ||| (b[5]!.toNat <<< 8))
  if cell != 32 && cell != 48 && cell != 64 then throw (IO.userError s!"{path}: cell {cell}")
  let emoji ← match ← (Emoji.load).toBaseIO with
    | .ok e => pure e
    | .error err => do IO.eprintln s!"no colour emoji: {err}"; pure default
  let sourceCell := cell
  let cell := pixelCell sourceCell density
  let noto ← Noto.load cell
  let sizes := [11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 32, 48, 56].foldl (fun out dp =>
    let px := (dp * density + 80) / 160
    out.insert px (noto.sized px)) ({} : Std.HashMap Nat Noto.Set)
  return ⟨b, cell, emoji, noto, sourceCell, sizes, ← Glyphs.load, false⟩

/-- Select a prepared size without IO, font parsing or raster scaling. -/
def Font.atSize (f : Font) (size : Nat) : Font :=
  match f.sizes[size]? with
  | some noto => { f with cell := size, noto }
  | none => f

/-- A glyph: where its 32 rows start in the file, and whether it is wide. -/
structure Glyph where
  at_ : Nat
  wide : Bool
  noto : Option Noto.Ref := none

/-- The font's glyph for code point c, if it has one. -/
@[inline] def Font.bitmapGlyph? (f : Font) (c : UInt32) : Option Glyph :=
  if c >= 0x20000 then none else
  let w := f.u32 (8 + 4 * c.toNat)
  if w == 0 then none
  else some ⟨tableEnd + ((w &&& 0x7FFFFFFF) - 1).toNat, w &&& 0x80000000 != 0, none⟩

/-- Noto supplies a real advance; fallback preserves the bitmap glyph. -/
@[inline] def Font.glyph? (f : Font) (c : UInt32) : Option Glyph :=
  match f.noto.chars[c]? with
  | some r => some ⟨0, false, some r⟩
  | none => f.bitmapGlyph? c

/-- What a missing code point shows: the replacement character. -/
def Font.glyph (f : Font) (c : UInt32) : Glyph :=
  match f.glyph? c with
  | some g => g
  | none => (f.glyph? 0xFFFD).getD ⟨tableEnd, false, none⟩

/-- Row r (0 .. cell - 1) of a glyph, its leftmost pixel in bit 63. -/
@[inline] def Font.row (f : Font) (g : Glyph) (r : Nat) : UInt64 := Id.run do
  let b := f.bytes
  let n := (if g.wide then f.sourceCell else f.sourceCell / 2) / 8
  let i := g.at_ + n * (r * f.sourceCell / f.cell)
  let mut v : UInt64 := 0
  for k in [0:n] do
    v := v ||| (b[i + k]!.toUInt64 <<< (56 - 8 * k).toUInt64)
  if f.cell == f.sourceCell then return v
  let mut scaled : UInt64 := 0
  for x in [0:if g.wide then f.cell else f.cell / 2] do
    if v &&& (0x8000000000000000 >>> (x * f.sourceCell / f.cell).toUInt64) != 0 then
      scaled := scaled ||| (0x8000000000000000 >>> x.toUInt64)
  return scaled

/-- A glyph's hmtx advance, or the fallback's half/full cell. -/
def Font.adv (f : Font) (g : Glyph) : Nat :=
  match g.noto with
  | some r => if f.fineMetrics then (r.unitsAdvance * f.cell + r.units / 2) / r.units else r.advance
  | none => if g.wide then f.cell else f.cell / 2

end Font
