/-
Bounded big-endian reads. Every byte access carries a checked index;
subtables are sliced only after checking their entire extent. No parser
uses machine-word offset arithmetic. Laws are in Ttf.Laws.
-/
import Std

namespace Ttf

@[inline] def u8 (b : ByteArray) (i : Nat) : Option Nat :=
  if h : i < b.size then some b[i].toNat else none

@[inline] def u16 (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u8 b i) * 256 + (← u8 b (i + 1))

@[inline] def u32 (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u16 b i) * 65536 + (← u16 b (i + 2))

@[inline] def signed (n : Nat) (bits : Nat) : Int :=
  if n < 2 ^ (bits - 1) then n else (n : Int) - (2 ^ bits : Nat)

@[inline] def i16 (b : ByteArray) (i : Nat) : Option Int :=
  (u16 b i).map (signed · 16)

def slice (b : ByteArray) (at_ len : Nat) : Option ByteArray :=
  if at_ + len ≤ b.size then some (b.extract at_ (at_ + len)) else none

/-- A table is confined to its declared length, including all nested reads. -/
def table (b : ByteArray) (tag : Nat) : Option ByteArray := do
  let n ← u16 b 4
  if n > 128 then none else do
    let _ ← slice b 12 (16 * n)
    let mut found := none
    for k in [0:n] do
      let at_ := 12 + 16 * k
      let t ← u32 b at_
      let start ← u32 b (at_ + 8)
      let len ← u32 b (at_ + 12)
      let bytes ← slice b start len
      if t == tag then
        if found.isSome then failure
        found := some bytes
    found

end Ttf
