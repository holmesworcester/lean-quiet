/-
Common CJK faces, subset from pinned Google Fonts Regular glyf instances.
The app has no language tag: Han prefers SC, then TC, JP, KR. Kana uses
JP, Hangul uses KR, Bopomofo uses TC; punctuation defaults to SC. Missing
subset characters remain on Unifont. Text's shaping/layout is untouched.
-/
import engine.renderer.Ttf.Read

namespace Cjk

def names : Array String := #["NotoSansSC-Common", "NotoSansTC-Common", "NotoSansJP-Common", "NotoSansKR-Common"]

def between (c lo hi : Nat) : Bool := lo ≤ c && c ≤ hi

def supported (c : Nat) : Bool :=
  between c 0x3000 0x31FF || between c 0x3400 0x9FFF ||
  between c 0xAC00 0xD7A3 || between c 0xF900 0xFAFF || between c 0xFF00 0xFFEF

/-- Locale priority is independent of the order the font files load. -/
def order (c : Nat) : List Nat :=
  if between c 0x3040 0x30FF || between c 0x31F0 0x31FF || between c 0xFF61 0xFF9F then [2]
  else if between c 0x3130 0x318F || between c 0xAC00 0xD7A3 || between c 0xFFA0 0xFFDC then [3]
  else if between c 0x3100 0x312F || between c 0x31A0 0x31BF then [1]
  else [0,1,2,3]

def choose (faces : Array Ttf.Face) (c : Nat) : Option (Nat × Nat) := do
  if !supported c then failure
  for i in order c do
    if let some f := faces[i]? then
      if let some g := Ttf.lookup f.cmap c then
        if g != 0 then return (i,g)
  failure

end Cjk
