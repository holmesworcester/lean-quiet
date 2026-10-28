/-
Every glyph the font draws without ink is a character names cannot tell
apart: it must be drawn as nothing (`Text.isInvisible`) or count as a
space (`Community.isBlank`), so that two names differing only by it are
marked Duplicate (Community.nameLook). Scans assets/font.bin whole; run
again whenever the font changes.

    inkless
-/
import ops.community.Facts
import engine.renderer.Text

def hex (c : UInt32) : String := String.ofList (Nat.toDigits 16 c.toNat)

def main : IO UInt32 := do
  let f ← Font.load
  let mut bad := #[]
  let mut blank := 0
  for c in [0:0x20000] do
    let c := c.toUInt32
    let some g := f.glyph? c | continue
    let mut ink := false
    for r in [0:f.cell] do
      if f.row g r != 0 then ink := true
    if !ink then
      blank := blank + 1
      if !Text.isInvisible c && !Community.isBlank c then bad := bad.push c
  if bad.isEmpty then
    IO.println s!"ok   every one of the font's {blank} inkless glyphs is invisible or a space"
    return 0
  IO.println s!"FAIL inkless glyphs names cannot tell apart, neither invisible nor a space: {bad.toList.map hex}"
  return 1
