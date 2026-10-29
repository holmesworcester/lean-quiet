/-
Every inkless glyph must be invisible or a space for name comparison.
Scan the loaded Font's complete routed repertoire, every Unifont fallback,
and every emoji picture through Paint.Bitmap.glyph at the app's cell size.
Source.bitmap supplies Noto's declared overhang for the canvas; the actual
painter does the lookup, rasterization and blit. Nothing parses fonts here.

    lake build inkless && .lake/build/bin/inkless
-/
import ops.community.Facts
import engine.renderer.Paint

namespace Inkless

private def hex (c : UInt32) : String :=
  let ds := Nat.toDigits 16 c.toNat
  "U+" ++ (String.ofList (List.replicate (4 - ds.length) '0' ++ ds)).toUpper

/-- Include the whole declared overhang, so clipping cannot hide ink.
Check both backgrounds for emoji, whose own colour may be white or black. -/
private def hasInk (f : Font.Font) (c : UInt32) : Bool := Id.run do
  let ink := if Emoji.isEmoji c then none else (f.glyph c).noto >>= f.noto.bitmap
  let picture := if Emoji.isEmoji c then f.emoji.picture c else none
  let left := ink.map (·.left) |>.getD 0
  let top := ink.map (·.top) |>.getD 0
  let w := left + max (2 * f.cell) (ink.map (fun b => b.advance + b.right) |>.getD 0)
  let h := top + f.cell + (ink.map (·.bottom) |>.getD 0)
  let w := max w (left + (picture.map (·.w.toNat) |>.getD 0))
  let h := max h (top + (picture.map (·.h.toNat) |>.getD 0))
  for bg in [0xFFFFFF, 0] do
    let row := Paint.solid bg w
    let b := Paint.Bitmap.blank w h row
    let painted := b.glyph f c left top (bg ^^^ 0xFFFFFF) false
    if painted.rows.any (· != row) then return true
  return false

/-- An inkless name character must actually normalize as its class says. -/
private def normalized (f : Font.Font) (c : UInt32) : Bool := Id.run do
  let ch := String.singleton (Char.ofNat c.toNat)
  if Text.isInvisible c then
    return (Text.place f #[c]).1.isEmpty &&
      Community.nameLook ("a" ++ ch ++ "b") == Community.nameLook "ab"
  else if Community.isBlank c then
    return Community.nameLook ("a" ++ ch ++ "b") == Community.nameLook "a b" &&
      Community.nameLook (ch ++ "a" ++ ch) == Community.nameLook "a"
  else return false

private structure Scan where
  count : Nat := 0
  blank : Nat := 0
  bad : Array String := #[]

private def test (s : Scan) (f : Font.Font) (c : UInt32) (source : String) : Scan := Id.run do
  let s := { s with count := s.count + 1 }
  if hasInk f c then return s
  let s := { s with blank := s.blank + 1 }
  if normalized f c then return s
  return { s with bad := s.bad.push s!"{hex c} ({source})" }

def run : IO UInt32 := do
  let f ← Font.load
  let names := (Noto.names.map (· ++ "-Regular")) ++ Cjk.names
  unless f.noto.faces.size == names.size && !f.emoji.entries.isEmpty do
    throw (IO.userError "inkless: missing runtime font/emoji assets")
  let mut faces := Array.replicate names.size 0
  let mut routed : Scan := {}
  let mut fallback : Scan := {}
  let bitmapOnly := { f with noto := {} }
  -- Enumerate Unicode, not a guessed Noto range. Unmapped characters use
  -- the replacement glyph, checked below; every mapped code point is tested.
  for n in [0:0x110000] do
    let c := n.toUInt32
    if let some g := f.glyph? c then
      let source := match g.noto with
        | some r => names[r.face]?.getD "invalid face"
        | none => "Unifont"
      if let some r := g.noto then faces := faces.modify r.face (· + 1)
      routed := test routed f c source
    if (f.bitmapGlyph? c).isSome then
      fallback := test fallback bitmapOnly c "Unifont fallback"
  for i in [0:names.size] do
    IO.println s!"inkless face {names[i]!}: {faces[i]!} routed codepoints"
    unless faces[i]! > 0 do throw (IO.userError s!"inkless: untested face {names[i]!}")
  let mut emoji : Scan := {}
  for i in [0:f.emoji.entries.size] do
    emoji := test emoji f (Emoji.base + i.toUInt32) "emoji picture"
  -- An absent glyph takes this same replacement through Font.glyph.
  unless (f.glyph? 0xE0000).isNone && hasInk f 0xE0000 && hasInk bitmapOnly 0xE0000 do
    throw (IO.userError "inkless: missing-glyph replacement is not visible")
  IO.println s!"inkless: cell {f.cell}px; {names.size} Noto faces; {routed.count} routed codepoints ({routed.blank} inkless); {fallback.count} Unifont fallbacks ({fallback.blank} inkless); {emoji.count} emoji pictures ({emoji.blank} inkless); both replacements visible"
  let bad := routed.bad ++ fallback.bad ++ emoji.bad
  if bad.isEmpty then
    IO.println "ok   every inkless glyph is invisible or a space, and its name normalizes accordingly"
    return 0
  IO.println s!"FAIL inkless glyphs names cannot tell apart: {bad.toList}"
  return 1

end Inkless

def main : IO UInt32 := Inkless.run
