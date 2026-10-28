/-
Segments: the data stream inside a symbol (ISO/IEC 18004 §7.4).

A symbol's data codewords are a bit stream of segments, each a 4-bit
mode, a count and the data, ended by a terminator (up to four zero bits),
zeros to the byte and pad bytes. This writes segments (`Seg.bits`,
`dataStream`) and reads them back (`parse`). Supported modes: numeric
(three digits in 10 bits), alphanumeric (two characters in 11 bits), byte,
and ECI, which `parse` passes through. Kanji, structured append and FNC1
are refused (`none`).

`parse` reads lists by pattern matching only, so there is no index to
get wrong. It is defined by well-founded recursion on the bits left
(every segment consumes its 4-bit mode), not with fuel or `partial`.
-/
import engine.renderer.qr.Bits
import engine.renderer.qr.Tables

namespace Qr

/-- A segment. Numeric and alphanumeric data are ASCII bytes. -/
inductive Seg where
  | numeric (ds : List UInt8)
  | alnum (cs : List UInt8)
  | bytes (bs : List UInt8)
  | eci (n : Nat)
  deriving Repr, DecidableEq

/-- The characters a segment stands for (an ECI stands for none). -/
def Seg.payload : Seg → List UInt8
  | .numeric ds | .alnum ds | .bytes ds => ds
  | .eci _ => []

def isDigit (c : UInt8) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The alphanumeric index of an ASCII character: `0-9`, `A-Z`, then
space `$ % * + - . / :`. -/
def alnumIdx (c : UInt8) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 90 then some (n - 55)
  else match n with
    | 32 => some 36 | 36 => some 37 | 37 => some 38 | 42 => some 39 | 43 => some 40
    | 45 => some 41 | 46 => some 42 | 47 => some 43 | 58 => some 44 | _ => none

/-- The character of an alphanumeric index. -/
def alnumChr (i : Nat) : UInt8 :=
  if i < 10 then (i + 48).toUInt8
  else if i < 36 then (i + 55).toUInt8
  else (([32, 36, 37, 42, 43, 45, 46, 47, 58] : List Nat).getD (i - 36) 0).toUInt8

def dv (c : UInt8) : Nat := c.toNat - 48
def av (c : UInt8) : Nat := (alnumIdx c).getD 0
def dig (d : Nat) : UInt8 := (d + 48).toUInt8

/-- Digits: three in 10 bits, a last two in 7, a last one in 4. -/
def numBits : List UInt8 → List Bool
  | a :: b :: c :: r => bitsOf (100 * dv a + 10 * dv b + dv c) 10 ++ numBits r
  | [a, b] => bitsOf (10 * dv a + dv b) 7
  | [a] => bitsOf (dv a) 4
  | [] => []

/-- Alphanumeric characters: two in 11 bits, a last one in 6. -/
def alnumBits : List UInt8 → List Bool
  | a :: b :: r => bitsOf (45 * av a + av b) 11 ++ alnumBits r
  | [a] => bitsOf (av a) 6
  | [] => []

/-- An ECI designator: one, two or three bytes, led by `0`, `10`, `110`. -/
def eciBits (n : Nat) : List Bool :=
  if n < 128 then false :: bitsOf n 7
  else if n < 16384 then true :: false :: bitsOf n 14
  else true :: true :: false :: bitsOf n 21

def Seg.mode : Seg → Nat
  | .numeric _ => 1 | .alnum _ => 2 | .bytes _ => 4 | .eci _ => 7

/-- A segment after its mode: count and data. -/
def Seg.body (v : Nat) : Seg → List Bool
  | .numeric ds => bitsOf ds.length (countWidth v 0) ++ numBits ds
  | .alnum cs => bitsOf cs.length (countWidth v 1) ++ alnumBits cs
  | .bytes bs => bitsOf bs.length (countWidth v 2) ++ bytesBits bs
  | .eci n => eciBits n

def Seg.bits (v : Nat) (s : Seg) : List Bool := bitsOf s.mode 4 ++ s.body v

def segsBits (v : Nat) (ss : List Seg) : List Bool := ss.flatMap (Seg.bits v)

/-- What a version-`v` symbol can carry: counts that fit their field,
digits that are digits, characters of the alphanumeric set, and ECI
assignment numbers below 10⁶. -/
def Seg.Valid (v : Nat) : Seg → Prop
  | .numeric ds => ds.length < 2 ^ countWidth v 0 ∧ ∀ d ∈ ds, isDigit d = true
  | .alnum cs => cs.length < 2 ^ countWidth v 1 ∧ ∀ c ∈ cs, (alnumIdx c).isSome = true
  | .bytes bs => bs.length < 2 ^ countWidth v 2
  | .eci n => n < 1000000

/-! ## Reading -/

def readNum : Nat → List Bool → Option (List UInt8 × List Bool)
  | 0, bs => some ([], bs)
  | 1, bs => match readBits 4 bs with
    | some (x, r) => if x < 10 then some ([dig x], r) else none
    | none => none
  | 2, bs => match readBits 7 bs with
    | some (x, r) => if x < 100 then some ([dig (x / 10), dig (x % 10)], r) else none
    | none => none
  | n + 3, bs => match readBits 10 bs with
    | some (x, r) =>
      if x < 1000 then
        match readNum n r with
        | some (ds, r) => some (dig (x / 100) :: dig (x / 10 % 10) :: dig (x % 10) :: ds, r)
        | none => none
      else none
    | none => none

def readAlnum : Nat → List Bool → Option (List UInt8 × List Bool)
  | 0, bs => some ([], bs)
  | 1, bs => match readBits 6 bs with
    | some (x, r) => if x < 45 then some ([alnumChr x], r) else none
    | none => none
  | n + 2, bs => match readBits 11 bs with
    | some (x, r) =>
      if x < 2025 then
        match readAlnum n r with
        | some (cs, r) => some (alnumChr (x / 45) :: alnumChr (x % 45) :: cs, r)
        | none => none
      else none
    | none => none

def readBytes : Nat → List Bool → Option (List UInt8 × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => match readBits 8 bs with
    | some (x, r) =>
      match readBytes n r with
      | some (cs, r) => some (x.toUInt8 :: cs, r)
      | none => none
    | none => none

def readEci : List Bool → Option (Nat × List Bool)
  | false :: r => readBits 7 r
  | true :: false :: r => readBits 14 r
  | true :: true :: false :: r => match readBits 21 r with
    | some (x, r) => if x < 1000000 then some (x, r) else none
    | none => none
  | _ => none

/-- The segment of mode `m` at the start of `bs`, and the bits after it. -/
def readSeg (v : Nat) : Nat → List Bool → Option (Seg × List Bool)
  | 1, bs => match readBits (countWidth v 0) bs with
    | some (n, r) => match readNum n r with
      | some (ds, r) => some (.numeric ds, r)
      | none => none
    | none => none
  | 2, bs => match readBits (countWidth v 1) bs with
    | some (n, r) => match readAlnum n r with
      | some (cs, r) => some (.alnum cs, r)
      | none => none
    | none => none
  | 4, bs => match readBits (countWidth v 2) bs with
    | some (n, r) => match readBytes n r with
      | some (cs, r) => some (.bytes cs, r)
      | none => none
    | none => none
  | 7, bs => match readEci bs with
    | some (n, r) => some (.eci n, r)
    | none => none
  | _, _ => none

theorem readNum_length : ∀ {n : Nat} {bs r : List Bool} {ds : List UInt8},
    readNum n bs = some (ds, r) → r.length ≤ bs.length
  | 0, bs, r, ds, h => by simp [readNum] at h; simp [h]
  | 1, bs, r, ds, h => by
    simp only [readNum] at h; split at h
    · rename_i hr; split at h <;> simp at h; obtain ⟨-, rfl⟩ := h; have := readBits_length hr; omega
    · simp at h
  | 2, bs, r, ds, h => by
    simp only [readNum] at h; split at h
    · rename_i hr; split at h <;> simp at h; obtain ⟨-, rfl⟩ := h; have := readBits_length hr; omega
    · simp at h
  | n + 3, bs, r, ds, h => by
    simp only [readNum] at h; split at h
    · rename_i hr; split at h
      · split at h
        · rename_i hn; simp at h; obtain ⟨-, rfl⟩ := h; have := readNum_length hn; have := readBits_length hr
          omega
        · simp at h
      · simp at h
    · simp at h

theorem readAlnum_length : ∀ {n : Nat} {bs r : List Bool} {ds : List UInt8},
    readAlnum n bs = some (ds, r) → r.length ≤ bs.length
  | 0, bs, r, ds, h => by simp [readAlnum] at h; simp [h]
  | 1, bs, r, ds, h => by
    simp only [readAlnum] at h; split at h
    · rename_i hr; split at h <;> simp at h; obtain ⟨-, rfl⟩ := h; have := readBits_length hr; omega
    · simp at h
  | n + 2, bs, r, ds, h => by
    simp only [readAlnum] at h; split at h
    · rename_i hr; split at h
      · split at h
        · rename_i hn; simp at h; obtain ⟨-, rfl⟩ := h; have := readAlnum_length hn; have := readBits_length hr
          omega
        · simp at h
      · simp at h
    · simp at h

theorem readBytes_length : ∀ {n : Nat} {bs r : List Bool} {ds : List UInt8},
    readBytes n bs = some (ds, r) → r.length ≤ bs.length
  | 0, bs, r, ds, h => by simp [readBytes] at h; simp [h]
  | n + 1, bs, r, ds, h => by
    simp only [readBytes] at h; split at h
    · rename_i hr; split at h
      · rename_i hn; simp at h; obtain ⟨-, rfl⟩ := h; have := readBytes_length hn; have := readBits_length hr
        omega
      · simp at h
    · simp at h

theorem readEci_length {bs r : List Bool} {n : Nat} (h : readEci bs = some (n, r)) :
    r.length ≤ bs.length := by
  unfold readEci at h
  split at h
  · have := readBits_length h; simp; omega
  · have := readBits_length h; simp; omega
  · split at h
    · rename_i hr; split at h <;> simp at h; obtain ⟨-, rfl⟩ := h; have := readBits_length hr; simp; omega
    · simp at h
  · simp at h

theorem readSeg_length {v m : Nat} {bs r : List Bool} {s : Seg}
    (h : readSeg v m bs = some (s, r)) : r.length ≤ bs.length := by
  unfold readSeg at h
  split at h
  all_goals first
    | (simp at h; done)
    | skip
  · split at h
    · rename_i hr; split at h
      · rename_i hn; simp at h; obtain ⟨-, rfl⟩ := h; have := readNum_length hn; have := readBits_length hr; omega
      · simp at h
    · simp at h
  · split at h
    · rename_i hr; split at h
      · rename_i hn; simp at h; obtain ⟨-, rfl⟩ := h; have := readAlnum_length hn; have := readBits_length hr; omega
      · simp at h
    · simp at h
  · split at h
    · rename_i hr; split at h
      · rename_i hn; simp at h; obtain ⟨-, rfl⟩ := h; have := readBytes_length hn; have := readBits_length hr; omega
      · simp at h
    · simp at h
  · split at h
    · rename_i hr; simp at h; obtain ⟨-, rfl⟩ := h; have := readEci_length hr; omega
    · simp at h

/-- The segments of a data stream: read until the terminator (a zero mode)
or until fewer than four bits are left. -/
def parse (v : Nat) (bs : List Bool) : Option (List Seg) :=
  match h : readBits 4 bs with
  | none => some []
  | some (m, r) =>
    if m = 0 then some []
    else
      match h2 : readSeg v m r with
      | none => none
      | some (s, r') => (parse v r').map (s :: ·)
termination_by bs.length
decreasing_by
  have := readBits_length h
  have := readSeg_length h2
  omega

/-- The characters of a data stream. -/
def payloadOf (ss : List Seg) : List UInt8 := ss.flatMap Seg.payload

/-! ## Writing a data stream -/

/-- Pad codewords: 0xEC and 0x11 by turns. -/
def padBytes (n : Nat) : List UInt8 :=
  (List.range n).map fun i => if i % 2 = 0 then 0xEC else 0x11

/-- The `cap` data codewords of segments: their bits, a terminator of up
to four zeros, zeros to the byte, then pad bytes; `none` if they do not
fit. -/
def dataStream (v cap : Nat) (ss : List Seg) : Option (List UInt8) :=
  let bs := segsBits v ss
  if bs.length ≤ 8 * cap then
    let t := bs ++ List.replicate (min 4 (8 * cap - bs.length)) false
    let t := t ++ List.replicate ((8 - t.length % 8) % 8) false
    some (packBytes t ++ padBytes (cap - t.length / 8))
  else none

end Qr
