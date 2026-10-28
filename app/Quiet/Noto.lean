/-
Pinned Noto faces and font metrics beneath Text. CJK selection is in Cjk;
the process-wide, bounded raster cache is in Ttf.Cache/Memo. A font load
assigns identities, but layout never rasterizes or mutates the cache.
-/
import Quiet.Ttf.Memo
import Quiet.Cjk
import Quiet.Ttf.Index

namespace Noto

def names : Array String := #["NotoSans", "NotoSansArmenian", "NotoSansGeorgian",
  "NotoSansHebrew", "NotoSansArabic", "NotoSansThai", "NotoSansEthiopic",
  "NotoSansCherokee", "NotoSansCanadianAboriginal"]

structure Ref where
  face : Nat
  glyph : Nat
  advance : Nat
  deriving Inhabited

abbrev Cached := Ttf.Memo.Source

structure Set where
  faces : Array Cached := #[]
  chars : Std.HashMap UInt32 Ref := {}
  deriving Inhabited

/-- Restrict the core faces' incidental coverage. CJK is selected below;
Indic, Tibetan, Myanmar and Khmer keep fallback. -/
def supported (c : Nat) : Bool :=
  c < 0x900 || (0xE00 ≤ c && c ≤ 0xE7F) || (0x10A0 ≤ c && c ≤ 0x10FF) ||
  (0x1200 ≤ c && c ≤ 0x167F) || (0x18B0 ≤ c && c ≤ 0x18FF) ||
  (0x1C80 ≤ c && c ≤ 0x1CFF) || (0x1D00 ≤ c && c ≤ 0x2DFF) ||
  (0xA640 ≤ c && c ≤ 0xA69F) || (0xAB00 ≤ c && c ≤ 0xABBF) ||
  (0xFB00 ≤ c && c ≤ 0xFDFF) || (0xFE70 ≤ c && c ≤ 0xFEFF)

def Set.bitmap (s : Set) (r : Ref) : Option Ttf.Bitmap := do
  let f ← s.faces[r.face]?
  f.bitmap r.glyph

/-- Layout consumes a compact cmap/hmtx index. Face parsing and outline
validation are deferred to first paint; file reads measured about 1 ms. -/
def load (cell : Nat) (dir : String := "assets") : IO Set := do
  let some index := Ttf.Index.read (← IO.FS.readBinFile (dir ++ "/noto-index.bin"))
    | throw (IO.userError "invalid Noto metric index")
  let files := (names.map (· ++ "-Regular")) ++ Cjk.names
  if index.size != files.size then throw (IO.userError "Noto index face count")
  let mut out : Set := {}
  for i in [0:files.size] do
    let some name := files[i]? | throw (IO.userError "Noto face")
    let some metrics := index[i]? | throw (IO.userError "Noto index")
    let path := dir ++ "/" ++ name ++ ".ttf"
    let bytes ← IO.FS.readBinFile path
    if bytes.size != metrics.bytes then throw (IO.userError s!"{path}: index/font size mismatch")
    out := { out with faces := out.faces.push (← Ttf.Memo.source bytes cell cell) }
    for (c,g,a) in metrics.chars do
      if g == 0 then continue
      let take := if i < names.size then supported c && !out.chars.contains c.toUInt32
        else Cjk.supported c && (Cjk.order c).contains (i-names.size) &&
          match out.chars[c.toUInt32]? with
          | none => true
          | some old => (Cjk.order c).idxOf (i-names.size) < (Cjk.order c).idxOf (old.face-names.size)
      if take then
        out := { out with chars := out.chars.insert c.toUInt32 ⟨i, g, (a*cell+metrics.units/2)/metrics.units⟩ }
  return out

end Noto
