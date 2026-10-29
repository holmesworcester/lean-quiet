/-
Colour emoji: Noto Color Emoji's own pictures (assets/emoji.bin,
tools/emoji.py), singles and sequences, at the text's size.

Text meets them in `emojify`: the longest sequence the set draws, at each
position, becomes one code point in plane 15's private use area (`base`
plus its index), so wrapping, bidi and placing treat a family, a flag or
a thumbs up with a skin tone as one unit. Unicode's presentation rules
decide when a single character is an emoji: always for those that are
emoji by default (😂), and only with VS16 (U+FE0F) for those that are
text by default (©, ♥, ☀), which then stay Unifont text.

A picture is decoded when a row is painted (QOI, a few thousand pixels);
nothing is decoded ahead of use.
-/
import engine.renderer.Qoi
import Std.Data.HashMap

namespace Emoji

structure Entry where
  seq : List UInt32
  /-- An emoji by default (else only when VS16 follows). -/
  dflt : Bool
  w : Nat
  off : Nat
  len : Nat
  deriving Inhabited

structure Set where
  bytes : ByteArray
  size : Nat
  entries : Array Entry
  bySeq : Std.HashMap (List UInt32) Nat
  maxLen : Nat
  dataAt : Nat

instance : Inhabited Set := ⟨⟨.empty, 0, #[], {}, 0, 0⟩⟩

/-- Where emoji code points start: U+F0000 plus the entry's index. -/
def base : UInt32 := 0xF0000

def isEmoji (c : UInt32) : Bool := c ≥ base

@[inline] def u32 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat ||| (b[i+1]!.toNat <<< 8) ||| (b[i+2]!.toNat <<< 16) ||| (b[i+3]!.toNat <<< 24)

def load (path : String := "assets/emoji.bin") : IO Set := do
  let b ← IO.FS.readBinFile path
  if b.size < 12 || b.extract 0 4 != "QEMJ".toUTF8 then throw (IO.userError s!"{path}: not an emoji set")
  let n := u32 b 4
  let size := u32 b 8
  let mut i := 12
  let mut entries := Array.mkEmpty n
  let mut bySeq : Std.HashMap (List UInt32) Nat := {}
  let mut maxLen := 0
  for k in [0:n] do
    let len := b[i]!.toNat
    let mut seq := []
    for j in [0:len] do seq := seq ++ [(u32 b (i + 1 + 4 * j)).toUInt32]
    let at_ := i + 1 + 4 * len
    let dflt := b[at_]! == 1
    let w := b[at_ + 1]!.toNat ||| (b[at_ + 2]!.toNat <<< 8)
    let off := u32 b (at_ + 3)
    let ln := u32 b (at_ + 7)
    entries := entries.push ⟨seq, dflt, w, off, ln⟩
    bySeq := bySeq.insert seq k
    maxLen := max maxLen len
    i := at_ + 11
  return ⟨b, size, entries, bySeq, maxLen, i⟩

def vs16 : UInt32 := 0xFE0F

/-- The longest emoji sequence at each position as one code point. A
sequence may carry VS16s the set's own sequence leaves out: they are
tried both ways. -/
def Set.emojify (e : Set) (cs : Array UInt32) : Array UInt32 := Id.run do
  if e.entries.isEmpty then return cs
  let mut out := Array.mkEmpty cs.size
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    -- quick refusal: ASCII starts only keycaps, which need U+20E3
    if c < 0x80 && !(i + 1 < cs.size && (cs[i+1]! == 0x20E3 || cs[i+1]! == vs16)) then
      out := out.push c; i := i + 1; continue
    let mut found := none
    -- longest first: the sequence as written, then without its VS16s
    let hi := min e.maxLen (cs.size - i) + 2
    for len in (List.range hi).reverse do
      if len < 2 || i + len > cs.size || found.isSome then continue
      let raw := (cs.extract i (i + len)).toList
      let k := e.bySeq[raw]? <|> e.bySeq[raw.filter (· != vs16)]?
      if let some k := k then
        if (raw.filter (· != vs16)).length ≥ 2 then found := some (k, len)
    match found with
    | some (k, len) => out := out.push (base + k.toUInt32); i := i + len
    | none =>
      match e.bySeq[[c]]? with
      | some k =>
        let withVs := i + 1 < cs.size && cs[i+1]! == vs16
        if e.entries[k]!.dflt || withVs then
          out := out.push (base + k.toUInt32); i := i + (if withVs then 2 else 1)
        else out := out.push c; i := i + 1
      | none => out := out.push c; i := i + 1
  return out

def Set.width (e : Set) (c : UInt32) : Nat :=
  (e.entries[(c - base).toNat]?.map (·.w)).getD e.size

/-- Asset pixels scale with the same density-adjusted cell as text. -/
def Set.scale (e : Set) (cell pixels : Nat) : Nat :=
  max 1 ((pixels * cell + e.size / 2) / max 1 e.size)

/-- The picture of emoji code point c: width, height and packed RGBA
pixels (r << 24 | g << 16 | b << 8 | a), decoded now. -/
def Set.picture (e : Set) (c : UInt32) : Option Qoi.Qoi := do
  let en ← e.entries[(c - base).toNat]?
  Qoi.decode (e.bytes.extract (e.dataAt + en.off) (e.dataAt + en.off + en.len))

end Emoji
