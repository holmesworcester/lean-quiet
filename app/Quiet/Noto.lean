/-
The installed Noto faces at one pixel size. The cache key is
(face index, glyph id, size); one memoizing Lean Thunk per key is shared
by all code points and paint tasks. Metrics never force a raster.
Reordering/stacking scripts and CFF CJK remain on Unifont.
-/
import Quiet.Ttf.Raster

namespace Noto

def names : Array String := #["NotoSans", "NotoSansArmenian", "NotoSansGeorgian",
  "NotoSansHebrew", "NotoSansArabic", "NotoSansThai", "NotoSansEthiopic",
  "NotoSansCherokee", "NotoSansCanadianAboriginal"]

structure Ref where
  face : Nat
  glyph : Nat
  advance : Nat
  deriving Inhabited

structure Cached where
  font : Ttf.Face
  size : Nat
  glyphs : Array (Thunk (Option Ttf.Bitmap))
  deriving Inhabited

structure Set where
  faces : Array Cached := #[]
  chars : Std.HashMap UInt32 Ref := {}
  deriving Inhabited

def cache (font : Ttf.Face) (size cell : Nat) : Cached :=
  ⟨font, size, (List.range font.advances.size).toArray.map fun g =>
    Thunk.mk fun _ => Ttf.raster font g size cell⟩

/-- Restrict the generic face's incidental coverage as well as the
specialist faces. Indic, Tibetan, Myanmar, Khmer and CJK keep fallback. -/
def supported (c : Nat) : Bool :=
  c < 0x900 || (0xE00 ≤ c && c ≤ 0xE7F) || (0x10A0 ≤ c && c ≤ 0x10FF) ||
  (0x1200 ≤ c && c ≤ 0x167F) || (0x18B0 ≤ c && c ≤ 0x18FF) ||
  (0x1C80 ≤ c && c ≤ 0x1CFF) || (0x1D00 ≤ c && c ≤ 0x2DFF) ||
  (0xA640 ≤ c && c ≤ 0xA69F) || (0xAB00 ≤ c && c ≤ 0xABBF) ||
  (0xFB00 ≤ c && c ≤ 0xFDFF) || (0xFE70 ≤ c && c ≤ 0xFEFF)

def Set.bitmap (s : Set) (r : Ref) : Option Ttf.Bitmap := do
  let f ← s.faces[r.face]?
  let g ← f.glyphs[r.glyph]?
  g.get

def load (cell : Nat) (dir : String := "assets") : IO Set := do
  let mut out : Set := {}
  for name in names do
    let path := dir ++ "/" ++ name ++ "-Regular.ttf"
    let bytes ← IO.FS.readBinFile path
    let some font := Ttf.read bytes | throw (IO.userError s!"{path}: invalid TrueType font")
    let face := out.faces.size
    out := { out with faces := out.faces.push (cache font cell cell) }
    for e in font.cmap do
      for c in [e.lo:e.hi + 1] do
        let glyph := e.glyph c
        if supported c && glyph != 0 && !out.chars.contains c.toUInt32 then
          out := { out with chars := out.chars.insert c.toUInt32 ⟨face, glyph, Ttf.advance font glyph cell⟩ }
  return out

end Noto
