/-
Unicode cmap formats 4 and 12. Each entry retains the table's range,
delta, or glyph array; lookup uses exactly that formula (cmap_entry in
Laws). The reader rejects unordered, overlapping and out-of-range maps.
-/
import Quiet.Ttf.Bytes

namespace Ttf

inductive Mapping where
  | delta (d : Int)
  | glyphs (ids : Array Nat) (d : Int)
  | sequential (first : Nat)
  deriving Inhabited

structure Entry where
  lo : Nat
  hi : Nat
  mapping : Mapping
  deriving Inhabited

def Entry.glyph (e : Entry) (c : Nat) : Nat :=
  match e.mapping with
  | .delta d => ((c : Int) + d).emod 65536 |>.toNat
  | .glyphs ids d =>
    let g := ids[c - e.lo]?.getD 0
    if g == 0 then 0 else ((g : Int) + d).emod 65536 |>.toNat
  | .sequential first => first + c - e.lo

def Entry.contains (e : Entry) (c : Nat) : Bool := e.lo ≤ c && c ≤ e.hi

abbrev Cmap := List Entry

def lookup (es : Cmap) (c : Nat) : Option Nat :=
  (es.find? (·.contains c)).map (·.glyph c)

def cmap4 (b : ByteArray) : Option Cmap := do
  let len ← u16 b 2
  let b ← slice b 0 len
  let twice ← u16 b 6
  if twice == 0 || twice % 2 != 0 || twice > 16378 then failure
  let n := twice / 2
  let _ ← slice b 14 (8 * n + 2)
  if (← u16 b (14 + 2 * n)) != 0 then failure
  let mut entries := []
  let mut prev := 0
  for k in [0:n] do
    let hi ← u16 b (14 + 2 * k)
    let lo ← u16 b (16 + 2 * n + 2 * k)
    let d ← i16 b (16 + 4 * n + 2 * k)
    let addr := 16 + 6 * n + 2 * k
    let off ← u16 b addr
    if lo > hi || (k > 0 && lo ≤ prev) || off % 2 != 0 then failure
    let mapping ← if off == 0 then pure (.delta d) else do
      if addr + off < 16 + 8 * n then none else do
        let mut ids := #[]
        for j in [0:hi - lo + 1] do
          ids := ids.push (← u16 b (addr + off + 2 * j))
        pure (.glyphs ids d)
    entries := ⟨lo, hi, mapping⟩ :: entries
    prev := hi
  if prev != 65535 then failure
  return entries.reverse

def cmap12 (b : ByteArray) : Option Cmap := do
  if (← u16 b 2) != 0 then failure
  let len ← u32 b 4
  let b ← slice b 0 len
  let n ← u32 b 12
  if n > 65536 then failure
  let _ ← slice b 16 (12 * n)
  let mut entries := []
  let mut prev := 0
  for k in [0:n] do
    let lo ← u32 b (16 + 12 * k)
    let hi ← u32 b (20 + 12 * k)
    let first ← u32 b (24 + 12 * k)
    if lo > hi || hi > 0x10FFFF || (k > 0 && lo ≤ prev) || first + hi - lo > 65535 then failure
    entries := ⟨lo, hi, .sequential first⟩ :: entries
    prev := hi
  return entries.reverse

def readCmap (b : ByteArray) : Option Cmap := do
  if (← u16 b 0) != 0 then failure
  let n ← u16 b 2
  if n > 128 then failure
  let mut best : Option Cmap := none
  let mut rank := 0
  for k in [0:n] do
    let platform ← u16 b (4 + 8 * k)
    let enc ← u16 b (6 + 8 * k)
    let off ← u32 b (8 + 8 * k)
    let sub ← slice b off (b.size - off)
    let format ← u16 sub 0
    if platform == 0 || (platform == 3 && (enc == 1 || enc == 10)) then
      if format == 12 then
        best := some (← cmap12 sub)
        rank := 12
      else if format == 4 && rank < 12 then
        best := some (← cmap4 sub)
        rank := 4
  best

end Ttf
