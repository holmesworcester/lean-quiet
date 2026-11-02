/-
Pinned Noto faces and font metrics beneath Text. CJK selection is in Cjk;
each face's glyph memo is in Ttf.Memo. Layout never rasterizes.
-/
import engine.renderer.Ttf.Memo
import engine.renderer.Cjk
import engine.renderer.Ttf.Index

namespace Noto

def names : Array String := #["NotoSans", "NotoSansArmenian", "NotoSansGeorgian",
  "NotoSansHebrew", "NotoSansArabic", "NotoSansThai", "NotoSansEthiopic",
  "NotoSansCherokee", "NotoSansCanadianAboriginal"]

structure Ref where
  face : Nat
  glyph : Nat
  advance : Nat
  unitsAdvance : Nat := 0
  units : Nat := 1
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

/-- Prepare a typography size once, sharing source bytes and parsed faces.
Advances use original hmtx units, never rescale rounded pixel advances. -/
def Set.sized (s : Set) (cell : Nat) : Set :=
  { faces := s.faces.map (·.sized cell cell)
    chars := s.chars.map fun _ r => { r with advance := (r.unitsAdvance * cell + r.units / 2) / r.units } }

/-- The same faces with empty glyph memos. -/
def Set.fresh (s : Set) : Set := { s with faces := s.faces.map (·.fresh) }

/-- Overlay a small typography face while retaining the shared script fallbacks. -/
def Set.overlay (s added : Set) : Set :=
  { faces := s.faces ++ added.faces
    chars := added.chars.toList.foldl (fun chars (code, r) =>
      chars.insert code { r with face := s.faces.size + r.face }) s.chars }

/-- Noto at every size: the regular faces at each pixel size 1..256, and
the medium ones over them at `mediumPx`, each made on first use. -/
structure Sizes where
  regular : Set := {}
  medium : Set := {}
  mediumPx : List Nat := []
  regularAt : Array (Thunk Set) := #[]
  mediumAt : Std.HashMap Nat (Thunk Set) := {}
  deriving Inhabited

def Sizes.make (regular medium : Set) (mediumPx : List Nat) : Sizes :=
  let regularAt := Array.ofFn (n := 257) fun px => Thunk.mk fun _ => regular.sized px.1
  { regular, medium, mediumPx, regularAt
    mediumAt := mediumPx.foldl (fun out px => out.insert px (Thunk.mk fun _ =>
      ((regularAt[px]?.map (·.get)).getD (regular.sized px)).overlay (medium.sized px))) {} }

/-- The same sizes with empty glyph memos: what the old ones kept is let go
once nothing holds them. -/
def Sizes.fresh (s : Sizes) : Sizes := make s.regular.fresh s.medium.fresh s.mediumPx

def medium (dir : String := "assets") : IO Set := do
  let some index := Ttf.Index.read (← IO.FS.readBinFile (dir ++ "/noto-ui-index.bin"))
    | throw (IO.userError "invalid UI font index")
  let some metrics := index[0]? | throw (IO.userError "missing UI font metrics")
  let bytes ← IO.FS.readBinFile (dir ++ "/NotoSans-UI-Medium.ttf")
  if bytes.size != metrics.bytes then throw (IO.userError "UI font/index size mismatch")
  let mut chars := ({} : Std.HashMap UInt32 Ref)
  for (c, g, a) in metrics.chars do
    if g != 0 then chars := chars.insert c.toUInt32 ⟨0, g, a, a, metrics.units⟩
  return ⟨#[Ttf.Memo.source bytes 1 1], chars⟩

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
    out := { out with faces := out.faces.push (Ttf.Memo.source bytes cell cell) }
    for (c,g,a) in metrics.chars do
      if g == 0 then continue
      let take := if i < names.size then supported c && !out.chars.contains c.toUInt32
        else Cjk.supported c && (Cjk.order c).contains (i-names.size) &&
          match out.chars[c.toUInt32]? with
          | none => true
          | some old => (Cjk.order c).idxOf (i-names.size) < (Cjk.order c).idxOf (old.face-names.size)
      if take then
        out := { out with chars := out.chars.insert c.toUInt32 ⟨i, g, (a*cell+metrics.units/2)/metrics.units, a, metrics.units⟩ }
  return out

end Noto
