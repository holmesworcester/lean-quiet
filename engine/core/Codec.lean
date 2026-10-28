/-
Canonical bytes, with decoding proven to invert encoding (`Codec.round`).
What the SQLite store writes is `encode` of a value, and what it reads
back is `decode` of those bytes, so an untampered database returns
exactly what was written (`decode_encode`).

`decode` is strict: it takes bytes only if they are exactly the
encoding of the value they decode to (`encode_decode`), as poc-17's
codec does. So a value has one byte string wherever it is read, from
SQLite, the wire, an op's body or a link, and nothing that hashes bytes
(an op's id) can be given a second name for the same value.

Numbers are LEB128 (seven bits a byte, low first); byte strings and
lists carry their length first; a sum carries its constructor's tag.

`enc` and `dec`, on lists, are the specification, and every law is
about them. What runs is a byte array: each codec also has `encInto`,
which appends a value's bytes to a buffer and must append exactly `enc`
(`encInto_eq`), and `decFrom`, which reads a value at an offset and must
read back any value whose bytes are there (`decFrom_at`). `encode` and
`decode` are compiled as `encodeFast` and `decodeFast`, which use only
those, through `@[csimp]` equalities (`encode_eq_fast`,
`decode_eq_fast`): proven, so every law about `encode` and `decode` is
a law about the code that runs. `decodeFast` keeps what `decFrom` read
only if encoding it again gives back the input, so it equals `decode`
on every input, whatever `decFrom` makes of bytes that encode nothing.
A byte string's length is read only while it still fits in the input
(`decLenFrom`), so a long length prefix builds no large number. A long
number is read and written by halves (`digitsFast`, `contDigitsInto`),
so one n bytes long costs O(n log n), not O(n²): a peer's 1 MiB number
is milliseconds, not minutes.

The number and byte-string readers are written over a monad and charge
what they do (`tick`; engine/core/Cost.lean): where they run (`Id`) the
meter is free, and counted (`Counted`) the same code gives its budget
(engine/core/CodecCost.lean): a number n bytes long costs O(n log n)
word operations, and a byte string's bytes are copied once, never read
one at a time.
-/
import engine.core.Cost

namespace Engine

namespace Codec

/-- Bytes l sit in b from offset i on. -/
def At (b : ByteArray) (i : Nat) (l : List UInt8) : Prop := l <+: b.data.toList.drop i

end Codec

class Codec (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Option (α × List UInt8)
  round : ∀ a rest, dec (enc a ++ rest) = some (a, rest)
  /-- What runs for `enc`: a's bytes appended to a buffer. -/
  encInto : ByteArray → α → ByteArray
  encInto_eq : ∀ buf a, (encInto buf a).data.toList = buf.data.toList ++ enc a
  /-- What runs for `dec`: the value whose bytes start at offset i of a
  byte array, and the offset after them. -/
  decFrom : ByteArray → Nat → Option (α × Nat)
  decFrom_at : ∀ {b i} a, Codec.At b i (enc a) → decFrom b i = some (a, i + (enc a).length)

namespace Codec

/-! ## Bytes at an offset -/

theorem At.left {b : ByteArray} {i : Nat} {l l' : List UInt8} (h : At b i (l ++ l')) : At b i l :=
  (List.prefix_append l l').trans h

theorem At.right {b : ByteArray} {i : Nat} {l l' : List UInt8} (h : At b i (l ++ l')) :
    At b (i + l.length) l' := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [← List.drop_drop, ← ht]
  simp

theorem At.cons {b : ByteArray} {i : Nat} {x : UInt8} {l : List UInt8} (h : At b i (x :: l)) :
    At b (i + 1) l :=
  At.right (l := [x]) h

theorem At.get {b : ByteArray} {i : Nat} {x : UInt8} {l : List UInt8} (h : At b i (x :: l)) :
    ∃ hi : i < b.size, b[i] = x := by
  obtain ⟨t, ht⟩ := h
  have h1 : (b.data.toList.drop i)[0]? = some x := by rw [← ht]; rfl
  rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_some_iff] at h1
  obtain ⟨hi, hx⟩ := h1
  exact ⟨by simpa using hi, hx⟩

theorem At.tag {b : ByteArray} {i : Nat} {x : UInt8} {l : List UInt8} (h : At b i (x :: l)) :
    b[i]? = some x := by
  obtain ⟨hi, hx⟩ := h.get
  rw [getElem?_pos b i hi, hx]

theorem At.length_le {b : ByteArray} {i : Nat} {l : List UInt8} (h : At b i l) : l.length ≤ b.size - i := by
  have := List.IsPrefix.length_le h
  simpa using this

theorem At.extract {b : ByteArray} {i : Nat} {x : ByteArray} (h : At b i x.data.toList) :
    b.extract i (i + x.size) = x := by
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left]
  have := List.prefix_iff_eq_take.1 h
  simp only [Array.length_toList, ByteArray.size_data] at this
  exact this.symm

theorem At.whole (b : ByteArray) : At b 0 b.data.toList := by
  simp [At]

theorem push_toList (buf : ByteArray) (x : UInt8) : (buf.push x).data.toList = buf.data.toList ++ [x] := by
  simp

/-! ## Numbers -/

def encNat (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encNat (n / 128)
termination_by n
decreasing_by omega

def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else (decNat rest).map fun p => (b.toNat - 128 + 128 * p.1, p.2)

theorem decNat_encNat (n : Nat) (rest : List UInt8) : decNat (encNat n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [encNat]
    by_cases h : n < 128
    · simp only [h, ite_true, List.singleton_append, decNat]
      have : n % 256 = n := Nat.mod_eq_of_lt (by omega)
      simp [this, h]
    · simp only [h, ite_false, List.cons_append, decNat]
      have h1 : (n % 128 + 128) % 256 = n % 128 + 128 := Nat.mod_eq_of_lt (by omega)
      have h2 : ¬ (n % 128 + 128 < 128) := by omega
      simp only [UInt8.toNat_ofNat', h1, h2, ite_false]
      rw [ih (n / 128) (by omega)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

theorem toNat_small {n : Nat} (h : n < 128) : n.toUInt8.toNat = n := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega

theorem toNat_big (n : Nat) : (n % 128 + 128).toUInt8.toNat = n % 128 + 128 := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega

theorem length_encNat_pos (n : Nat) : 0 < (encNat n).length := by
  rw [encNat]; split <;> simp

theorem encNat_small {n : Nat} (h : n < 128) : encNat n = [n.toUInt8] := by
  rw [encNat, ite_eq_left h]

theorem encNat_big {n : Nat} (h : ¬ n < 128) :
    encNat n = (n % 128 + 128).toUInt8 :: encNat (n / 128) := by
  rw [encNat, ite_eq_right h]

theorem two_pow_seven (k : Nat) : 2 ^ (7 * k) = 128 ^ k := by
  rw [Nat.pow_mul]

/-- What is left of x under its top bits from s up: x mod 2^s. -/
theorem sub_shift (x s : Nat) : x - ((x >>> s) <<< s) = x % 2 ^ s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have := Nat.div_add_mod x (2 ^ s)
  rw [Nat.mul_comm] at this
  omega

/-! ### Long numbers, by halves

A number's bytes are read and written in halves: its base-128 digits
are cut in two, each half is done the same way, and the halves are
joined with one shift and one add (or split with one shift and one
subtraction). A number n bytes long then costs O(n log n) word
operations, where a byte at a time costs O(n²): a 64 KiB number took a
second that way. Up to 8 digits (under 2^56) a number is a machine
word, and is done a byte at a time. -/

/-- The low h base-128 digits of x, low first, each with the
continuation bit: what an encoding holds before its high part. -/
def contDigits (x : Nat) : Nat → List UInt8
  | 0 => []
  | h + 1 => (x % 128 + 128).toUInt8 :: contDigits (x / 128) h

/-- **A number's encoding is its low digits, then its high part.** -/
theorem encNat_split : ∀ (h x y : Nat), x < 128 ^ h → 0 < y →
    encNat (x + 128 ^ h * y) = contDigits x h ++ encNat y
  | 0, x, y, hx, _ => by
    have : x = 0 := by simp at hx; omega
    subst this; simp [contDigits]
  | h + 1, x, y, hx, hy => by
    have e : x + 128 ^ (h + 1) * y = x + 128 * (128 ^ h * y) := by
      rw [Nat.pow_succ, Nat.mul_comm (128 ^ h) 128, Nat.mul_assoc]
    have hp : 0 < 128 ^ h := Nat.pow_pos (by decide : 0 < 128)
    have hge : 128 ≤ x + 128 * (128 ^ h * y) := by
      have : 1 ≤ 128 ^ h * y := Nat.mul_pos hp hy
      omega
    rw [e, encNat_big (by omega), Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ (by decide : 0 < 128)]
    have hx' : x / 128 < 128 ^ h := by
      rw [Nat.pow_succ] at hx
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    rw [encNat_split h (x / 128) y hx' hy]
    rfl

theorem contDigits_add : ∀ (k h x : Nat),
    contDigits x (k + h) = contDigits (x % 128 ^ k) k ++ contDigits (x / 128 ^ k) h
  | 0, h, x => by simp [contDigits]
  | k + 1, h, x => by
    rw [show k + 1 + h = (k + h) + 1 by omega, contDigits, contDigits_add k h (x / 128), contDigits]
    have hd : (128 : Nat) ∣ 128 ^ (k + 1) := Nat.dvd_of_mod_eq_zero (by simp [Nat.pow_succ])
    rw [Nat.mod_mod_of_dvd x hd, Nat.pow_succ, Nat.mul_comm (128 ^ k) 128,
      Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul]
    rfl

/-- `contDigits`, a byte at a time, into a buffer. -/
def contDigitsLoop (buf : ByteArray) (x : Nat) : Nat → ByteArray
  | 0 => buf
  | h + 1 => contDigitsLoop (buf.push (x % 128 + 128).toUInt8) (x / 128) h

theorem contDigitsLoop_eq : ∀ (buf : ByteArray) (x h : Nat),
    (contDigitsLoop buf x h).data.toList = buf.data.toList ++ contDigits x h
  | buf, x, 0 => by simp [contDigitsLoop, contDigits]
  | buf, x, h + 1 => by simp [contDigitsLoop, contDigits, contDigitsLoop_eq _ (x / 128) h]

/-- `contDigits`, by halves, into a buffer. -/
def contDigitsInto (buf : ByteArray) (x h : Nat) : ByteArray :=
  if h ≤ 8 then contDigitsLoop buf x h
  else
    let k := h / 2
    let y := x >>> (7 * k)
    contDigitsInto (contDigitsInto buf (x - (y <<< (7 * k))) k) y (h - k)
termination_by h
decreasing_by all_goals omega

theorem contDigitsInto_eq (buf : ByteArray) (x h : Nat) :
    (contDigitsInto buf x h).data.toList = buf.data.toList ++ contDigits x h := by
  induction h using Nat.strongRecOn generalizing buf x with
  | _ h ih =>
    rw [contDigitsInto]
    split
    · exact contDigitsLoop_eq buf x h
    · simp only
      rw [ih _ (by omega), ih _ (by omega), sub_shift, Nat.shiftRight_eq_div_pow, two_pow_seven,
        List.append_assoc, ← contDigits_add, show h / 2 + (h - h / 2) = h by omega]

def encNatInto (buf : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then buf.push n.toUInt8
  else if n < 2 ^ 56 then encNatInto (buf.push (n % 128 + 128).toUInt8) (n / 128)
  else
    let k := n.log2 / 14
    let y := n >>> (7 * k)
    encNatInto (contDigitsInto buf (n - (y <<< (7 * k))) k) y
termination_by n
decreasing_by
  · omega
  · rename_i h1 h2
    have hk : 4 ≤ n.log2 / 14 := by
      have := (Nat.le_log2 (by omega)).2 (Nat.le_of_not_lt h2)
      omega
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_self (by omega) (Nat.one_lt_two_pow (by omega))

theorem encNatInto_eq (buf : ByteArray) (n : Nat) :
    (encNatInto buf n).data.toList = buf.data.toList ++ encNat n := by
  induction n using Nat.strongRecOn generalizing buf with
  | _ n ih =>
    rw [encNatInto]
    split
    · rename_i h1; rw [encNat_small h1]; simp
    · split
      · rename_i h1 _; rw [ih _ (by omega), encNat_big h1]; simp
      · rename_i h1 h2
        simp only
        have hn : n ≠ 0 := by omega
        have hk : 4 ≤ n.log2 / 14 := by
          have := (Nat.le_log2 hn).2 (Nat.le_of_not_lt h2)
          omega
        have hle : 128 ^ (n.log2 / 14) ≤ n := by
          rw [← two_pow_seven]
          exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.log2_self_le hn)
        have hy : n >>> (7 * (n.log2 / 14)) < n := by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_lt_self (by omega) (Nat.one_lt_two_pow (by omega))
        rw [ih _ hy, contDigitsInto_eq, sub_shift, Nat.shiftRight_eq_div_pow, two_pow_seven,
          List.append_assoc, ← encNat_split _ _ _ (Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 128)))
            (Nat.div_pos hle (Nat.pow_pos (by decide : 0 < 128))), Nat.mod_add_div]

/-- Byte j of b as a number, or 0 past b's end. -/
def byteAt (b : ByteArray) (j : Nat) : Nat := if h : j < b.size then b[j].toNat else 0

/-- The number L base-128 digits from offset i spell, low first: each
byte's low seven bits. -/
def digits (b : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => byteAt b i % 128 + 128 * digits b (i + 1) L

theorem digits_add (b : ByteArray) : ∀ (k i L : Nat),
    digits b i (k + L) = digits b i k + digits b (i + k) L * 128 ^ k
  | 0, i, L => by simp [digits]
  | k + 1, i, L => by
    rw [show k + 1 + L = (k + L) + 1 by omega, digits, digits, digits_add b k (i + 1) L,
      show i + 1 + k = i + (k + 1) by omega, Nat.pow_succ, Nat.mul_add]
    generalize digits b (i + (k + 1)) L = y
    generalize 128 ^ k = p
    rw [Nat.mul_comm p 128, ← Nat.mul_assoc y 128 p, Nat.mul_comm y 128, Nat.mul_assoc 128 y p]
    omega

section
variable {m : Type → Type} [Monad m] [Tick m]

/-- `digits`, by halves, charged. Up to 8 digits a number is one machine
word, read a byte at a time: a word operation a digit. Above, joining
two halves into an L-digit number (a shift and an add of numbers of at
most L digits) is charged L. -/
def digitsM (b : ByteArray) (i L : Nat) : m Nat :=
  if L ≤ 8 then do
    tick { work := L }
    pure (digits b i L)
  else do
    let lo ← digitsM b i (L / 2)
    let hi ← digitsM b (i + L / 2) (L - L / 2)
    tick { work := L }
    pure (lo + (hi <<< (7 * (L / 2))))
termination_by L
decreasing_by all_goals omega

end

/-- `digits`, by halves: `digitsM` where it runs. -/
def digitsFast (b : ByteArray) (i L : Nat) : Nat := Id.run (digitsM b i L)

theorem digitsFast_unfold (b : ByteArray) (i L : Nat) :
    digitsFast b i L = if L ≤ 8 then digits b i L
      else digitsFast b i (L / 2) + (digitsFast b (i + L / 2) (L - L / 2) <<< (7 * (L / 2))) := by
  unfold digitsFast; rw [digitsM]; split <;> rfl

theorem digitsFast_eq (b : ByteArray) (L : Nat) : ∀ i, digitsFast b i L = digits b i L := by
  induction L using Nat.strongRecOn with
  | _ L ih =>
    intro i
    rw [digitsFast_unfold]
    split
    · rfl
    · rw [ih _ (by omega), ih _ (by omega), Nat.shiftLeft_eq, two_pow_seven, ← digits_add,
        show L / 2 + (L - L / 2) = L by omega]

section
variable {m : Type → Type} [Monad m] [Tick m]

/-- Where the number at offset i ends (its first byte under 128),
charged a word operation a byte read. -/
def numEndM (b : ByteArray) (i : Nat) : m (Option Nat) :=
  if h : i < b.size then do
    tick { work := 1 }
    if b[i].toNat < 128 then pure (some i) else numEndM b (i + 1)
  else pure none
termination_by b.size - i

/-- A number at offset i: where it ends, then its digits, by halves. -/
def decNatFromM (b : ByteArray) (i : Nat) : m (Option (Nat × Nat)) := do
  match ← numEndM b i with
  | some j =>
    let n ← digitsM b i (j + 1 - i)
    pure (some (n, j + 1))
  | none => pure none

end

/-- Where the number at offset i ends: `numEndM` where it runs. -/
def numEnd (b : ByteArray) (i : Nat) : Option Nat := Id.run (numEndM b i)

theorem numEnd_unfold (b : ByteArray) (i : Nat) :
    numEnd b i = if h : i < b.size then (if b[i].toNat < 128 then some i else numEnd b (i + 1)) else none := by
  unfold numEnd; rw [numEndM]; split
  · split <;> rfl
  · rfl

/-- A number at offset i: `decNatFromM` where it runs. -/
def decNatFrom (b : ByteArray) (i : Nat) : Option (Nat × Nat) := Id.run (decNatFromM b i)

theorem decNatFrom_unfold (b : ByteArray) (i : Nat) : decNatFrom b i =
    match numEnd b i with
    | some j => some (digitsFast b i (j + 1 - i), j + 1)
    | none => none := by
  unfold decNatFrom decNatFromM numEnd digitsFast
  generalize numEndM (m := Id) b i = x
  change Option Nat at x
  cases x <;> rfl

theorem numEnd_digits_at {b : ByteArray} (n : Nat) : ∀ {i : Nat}, At b i (encNat n) →
    numEnd b i = some (i + (encNat n).length - 1) ∧ digits b i (encNat n).length = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i h
    by_cases hn : n < 128
    · rw [encNat_small hn] at h ⊢
      obtain ⟨hi, hx⟩ := h.get
      have hb : byteAt b i = b[i].toNat := by simp [byteAt, hi]
      rw [numEnd_unfold, dite_eq_left hi, hx, toNat_small hn, ite_eq_left hn]
      simp [digits, hb, hx, toNat_small hn, Nat.mod_eq_of_lt hn]
    · rw [encNat_big hn] at h ⊢
      obtain ⟨hi, hx⟩ := h.get
      have hb : byteAt b i = b[i].toNat := by simp [byteAt, hi]
      obtain ⟨ih1, ih2⟩ := ih (n / 128) (by omega) h.cons
      have := length_encNat_pos (n / 128)
      rw [numEnd_unfold, dite_eq_left hi, hx, toNat_big, ite_eq_right (by omega), ih1]
      simp only [List.length_cons, digits, hb, hx, toNat_big, ih2]
      constructor
      · congr 1; omega
      · omega

theorem decNatFrom_at {b : ByteArray} {i : Nat} (n : Nat) (h : At b i (encNat n)) :
    decNatFrom b i = some (n, i + (encNat n).length) := by
  obtain ⟨h1, h2⟩ := numEnd_digits_at n h
  have := length_encNat_pos n
  rw [decNatFrom_unfold, h1]
  simp only
  rw [show i + (encNat n).length - 1 + 1 - i = (encNat n).length by omega, digitsFast_eq, h2]
  congr 2; omega

instance : Codec Nat where
  enc := encNat
  dec := decNat
  round := decNat_encNat
  encInto := encNatInto
  encInto_eq := encNatInto_eq
  decFrom := decNatFrom
  decFrom_at := decNatFrom_at

/-- A byte array's length at offset i, a byte at a time, given up as
soon as it could not fit in b: no length that fits is refused
(`decLenFrom_at`), and no large number is ever built. -/
def decLenFromM {m : Type → Type} [Monad m] [Tick m] (b : ByteArray) (i acc k : Nat) :
    m (Option (Nat × Nat)) :=
  if h : i < b.size then do
    tick { work := 1 }
    let x := b[i].toNat
    if x < 128 then pure (some (acc + x * k, i + 1))
    else if b.size < k * 128 then pure none
    else decLenFromM b (i + 1) (acc + (x - 128) * k) (k * 128)
  else pure none
termination_by b.size - i

/-- `decLenFromM` where it runs. -/
def decLenFrom (b : ByteArray) (i acc m : Nat) : Option (Nat × Nat) := Id.run (decLenFromM b i acc m)

theorem decLenFrom_unfold (b : ByteArray) (i acc m : Nat) : decLenFrom b i acc m =
    if h : i < b.size then
      let x := b[i].toNat
      if x < 128 then some (acc + x * m, i + 1)
      else if b.size < m * 128 then none
      else decLenFrom b (i + 1) (acc + (x - 128) * m) (m * 128)
    else none := by
  unfold decLenFrom; rw [decLenFromM]; split
  · simp only; split
    · rfl
    · split <;> rfl
  · rfl

theorem split128 (n acc m : Nat) : acc + (n % 128 + 128 - 128) * m + n / 128 * (m * 128) = acc + n * m := by
  rw [Nat.add_sub_cancel]
  have e := Nat.mod_add_div n 128
  have : n * m = n % 128 * m + n / 128 * (m * 128) := by
    conv => lhs; rw [← e]
    rw [Nat.add_mul, Nat.mul_comm 128 (n / 128), Nat.mul_assoc, Nat.mul_comm 128 m]
  omega

theorem decLenFrom_at {b : ByteArray} (n : Nat) : ∀ {i : Nat} (acc m : Nat), At b i (encNat n) →
    acc + n * m ≤ b.size → decLenFrom b i acc m = some (acc + n * m, i + (encNat n).length) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i acc m h hb
    rw [encNat] at h ⊢
    by_cases hn : n < 128
    · simp only [hn, ite_true] at h ⊢
      obtain ⟨hi, hx⟩ := h.get
      rw [decLenFrom_unfold, dite_eq_left hi]
      simp [hx, toNat_small hn, hn]
    · simp only [hn, ite_false] at h ⊢
      obtain ⟨hi, hx⟩ := h.get
      have hm : 128 * m ≤ n * m := Nat.mul_le_mul_right m (by omega)
      rw [decLenFrom_unfold, dite_eq_left hi]
      simp only [hx, toNat_big, show ¬ (n % 128 + 128 < 128) by omega, ite_false,
        show ¬ (b.size < m * 128) by omega]
      rw [ih (n / 128) (by omega) _ _ h.cons (by rw [split128]; exact hb), split128]
      simp only [List.length_cons]
      congr 2; omega

/-! ## Byte strings -/

def encBytesL (l : List UInt8) : List UInt8 := encNat l.length ++ l

def decBytesL (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match decNat bs with
  | none => none
  | some (n, rest) => if n ≤ rest.length then some (rest.take n, rest.drop n) else none

theorem decBytesL_encBytesL (l rest : List UInt8) : decBytesL (encBytesL l ++ rest) = some (l, rest) := by
  unfold decBytesL encBytesL
  rw [List.append_assoc, decNat_encNat]
  simp

/-- A byte string at offset i: its length, then its bytes, copied at
once (charged their count). -/
def decBytesFromM {m : Type → Type} [Monad m] [Tick m] (b : ByteArray) (i : Nat) :
    m (Option (ByteArray × Nat)) := do
  match ← decLenFromM b i 0 1 with
  | some (n, j) =>
    if j + n ≤ b.size then do
      tick { copied := n }
      pure (some (b.extract j (j + n), j + n))
    else pure none
  | none => pure none

/-- `decBytesFromM` where it runs. -/
def decBytesFrom (b : ByteArray) (i : Nat) : Option (ByteArray × Nat) := Id.run (decBytesFromM b i)

theorem decBytesFrom_unfold (b : ByteArray) (i : Nat) : decBytesFrom b i =
    match decLenFrom b i 0 1 with
    | some (n, j) => if j + n ≤ b.size then some (b.extract j (j + n), j + n) else none
    | none => none := by
  unfold decBytesFrom decBytesFromM decLenFrom
  generalize decLenFromM (m := Id) b i 0 1 = x
  change Option (Nat × Nat) at x
  rcases x with _ | ⟨n, j⟩
  · rfl
  · show Id.run (if j + n ≤ b.size then _ else _) = (if j + n ≤ b.size then _ else _)
    by_cases h : j + n ≤ b.size <;> simp only [h, ite_true, ite_false] <;> rfl

instance : Codec ByteArray where
  enc b := encBytesL b.data.toList
  dec bs := (decBytesL bs).map fun p => (⟨p.1.toArray⟩, p.2)
  round b rest := by
    rw [decBytesL_encBytesL]; simp
  encInto buf x := encNatInto buf x.size ++ x
  encInto_eq buf x := by simp [encNatInto_eq, encBytesL]
  decFrom := decBytesFrom
  decFrom_at x h := by
    have hl : x.data.toList.length = x.size := by simp
    simp only [encBytesL, hl] at h ⊢
    have hle := h.length_le
    have := length_encNat_pos x.size
    simp only [List.length_append, Array.length_toList, ByteArray.size_data] at hle
    rw [decBytesFrom_unfold, decLenFrom_at x.size 0 1 h.left (by omega)]
    simp only [Nat.zero_add, Nat.mul_one]
    rw [ite_eq_left (by omega), h.right.extract]
    simp only [List.length_append, Array.length_toList, ByteArray.size_data]
    congr 2; omega

/-! ## Small values -/

instance : Codec Bool where
  enc b := [if b then 1 else 0]
  dec | b :: rest => if b = 1 then some (true, rest) else if b = 0 then some (false, rest) else none
      | [] => none
  round b rest := by cases b <;> rfl
  encInto buf b := buf.push (if b then 1 else 0)
  encInto_eq buf b := push_toList _ _
  decFrom b i := match b[i]? with
    | some 1 => some (true, i + 1)
    | some 0 => some (false, i + 1)
    | _ => none
  decFrom_at x h := by cases x <;> simp [h.tag]

instance : Codec UInt8 where
  enc b := [b]
  dec | b :: rest => some (b, rest)
      | [] => none
  round _ _ := rfl
  encInto buf b := buf.push b
  encInto_eq buf b := push_toList _ _
  decFrom b i := (b[i]?).map fun x => (x, i + 1)
  decFrom_at x h := by simp [h.tag]

/-! ## Lists and pairs -/

def encList {α} [Codec α] : List α → List UInt8
  | [] => [0]
  | a :: t => 1 :: (enc a ++ encList t)

def decListF {α} [Codec α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, _ => none
  | _ + 1, 0 :: rest => some ([], rest)
  | n + 1, 1 :: rest => match dec rest with
    | none => none
    | some (a, r) => (decListF n r).map fun p => (a :: p.1, p.2)
  | _ + 1, _ => none

theorem decListF_encList {α} [Codec α] (l : List α) (rest : List UInt8) (n : Nat) (hn : l.length < n) :
    decListF n (encList l ++ rest) = some (l, rest) := by
  induction l generalizing n with
  | nil => cases n with
    | zero => simp at hn
    | succ n => rfl
  | cons a t ih => cases n with
    | zero => simp at hn
    | succ n =>
      simp only [encList, List.cons_append, decListF, List.append_assoc, round]
      rw [ih n (by simp at hn; omega)]; rfl

/-- A list's encoding is at least as long as the list, which bounds the
decoder's fuel. -/
theorem length_le_encList {α} [Codec α] (l : List α) : l.length < (encList l).length + 1 := by
  induction l with
  | nil => simp [encList]
  | cons a t ih => simp [encList]; omega

def encListInto {α} [Codec α] (buf : ByteArray) : List α → ByteArray
  | [] => buf.push 0
  | a :: t => encListInto (encInto (buf.push 1) a) t

theorem encListInto_eq {α} [Codec α] (buf : ByteArray) (l : List α) :
    (encListInto buf l).data.toList = buf.data.toList ++ encList l := by
  induction l generalizing buf with
  | nil => simp [encListInto, encList]
  | cons a t ih => simp [encListInto, encList, ih, encInto_eq]

/-- The rest of a list at offset i, its first items in `acc`; at most
`n` items more. -/
def decListFrom {α} [Codec α] (b : ByteArray) : Nat → Nat → Array α → Option (List α × Nat)
  | 0, _, _ => none
  | n + 1, i, acc =>
    if h : i < b.size then
      if b[i] = 0 then some (acc.toList, i + 1)
      else if b[i] = 1 then
        match (decFrom b (i + 1) : Option (α × Nat)) with
        | some (a, j) => decListFrom b n j (acc.push a)
        | none => none
      else none
    else none

theorem decListFrom_at {α} [Codec α] {b : ByteArray} (l : List α) : ∀ (n i : Nat) (acc : Array α),
    At b i (encList l) → l.length < n →
      decListFrom b n i acc = some (acc.toList ++ l, i + (encList l).length) := by
  induction l with
  | nil =>
    intro n i acc h hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨hi, hx⟩ := h.get
    simp [decListFrom, hi, hx, encList]
  | cons a t ih =>
    intro n i acc h hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [encList] at h ⊢
    obtain ⟨hi, hx⟩ := h.get
    have h1 := h.cons
    rw [decListFrom, dite_eq_left hi, hx, ite_eq_right (by decide), ite_eq_left rfl, decFrom_at a h1.left]
    dsimp only
    rw [ih k _ _ h1.right (by simp at hn; omega)]
    simp only [Array.toList_push, List.append_assoc, List.singleton_append, List.length_cons,
      List.length_append]
    congr 2; omega

instance {α} [Codec α] : Codec (List α) where
  enc := encList
  dec bs := decListF (bs.length + 1) bs
  round l rest := by
    apply decListF_encList
    have := length_le_encList l
    simp; omega
  encInto := encListInto
  encInto_eq := encListInto_eq
  decFrom b i := decListFrom b (b.size - i + 1) i #[]
  decFrom_at l h := by
    have := length_le_encList l
    have := h.length_le
    rw [decListFrom_at l _ _ _ h (by omega)]
    simp

def decPair {α β} [Codec α] [Codec β] (bs : List UInt8) : Option ((α × β) × List UInt8) :=
  match (dec bs : Option (α × List UInt8)) with
  | none => none
  | some (a, r) => match (dec r : Option (β × List UInt8)) with
    | none => none
    | some (b, r') => some ((a, b), r')

def decPairFrom {α β} [Codec α] [Codec β] (b : ByteArray) (i : Nat) : Option ((α × β) × Nat) :=
  match (decFrom b i : Option (α × Nat)) with
  | none => none
  | some (a, j) => match (decFrom b j : Option (β × Nat)) with
    | none => none
    | some (c, k) => some ((a, c), k)

instance {α β} [Codec α] [Codec β] : Codec (α × β) where
  enc p := enc p.1 ++ enc p.2
  dec := decPair
  round p rest := by
    unfold decPair
    rw [List.append_assoc, Codec.round p.1]
    simp only
    rw [Codec.round p.2]
  encInto buf p := encInto (encInto buf p.1) p.2
  encInto_eq buf p := by rw [encInto_eq, encInto_eq, List.append_assoc]
  decFrom := decPairFrom
  decFrom_at p h := by
    unfold decPairFrom
    rw [decFrom_at p.1 h.left]
    dsimp only
    rw [decFrom_at p.2 h.right]
    simp [Nat.add_assoc]

/-! ## Building codecs: a value read as another, a tag first -/

/-- The value at offset i read as α, then mapped by f. -/
def decFromAs {α β} [Codec α] (f : α → β) (b : ByteArray) (i : Nat) : Option (β × Nat) :=
  match (decFrom b i : Option (α × Nat)) with
  | none => none
  | some (a, j) => some (f a, j)

theorem decFromAs_at {α β} [Codec α] (f : α → β) {b : ByteArray} {i : Nat} {a : α}
    (h : At b i (enc a)) : decFromAs f b i = some (f a, i + (enc a).length) := by
  unfold decFromAs; rw [decFrom_at a h]

/-- After a tag at offset i, the value at i + 1 read as α and mapped. -/
theorem decFromAs_tag {α β} [Codec α] (f : α → β) {b : ByteArray} {i : Nat} {t : UInt8} {a : α}
    (h : At b i (t :: enc a)) : decFromAs f b (i + 1) = some (f a, i + (t :: enc a).length) := by
  rw [decFromAs_at f h.cons]
  simp only [List.length_cons]
  congr 2; omega

theorem encInto_tag {α} [Codec α] (buf : ByteArray) (t : UInt8) (a : α) :
    (encInto (buf.push t) a).data.toList = buf.data.toList ++ t :: enc a := by
  simp [encInto_eq]

/-! ## Whole values -/

/-- The bytes of a value. -/
def encode {α} [Codec α] (a : α) : ByteArray := ⟨(enc a).toArray⟩

/-- The value of bytes holding exactly one, if they are its encoding. -/
def decode {α} [Codec α] (b : ByteArray) : Option α :=
  match dec b.data.toList with
  | some (a, []) => if enc a = b.data.toList then some a else none
  | _ => none

theorem decode_encode {α} [Codec α] (a : α) : decode (encode a) = some a := by
  unfold decode encode
  have := round a []
  simp only [List.append_nil] at this
  simp [this]

/-- **Bytes decode only from their value's encoding**: a decoded value
has no other byte string. -/
theorem encode_decode {α} [Codec α] {b : ByteArray} {a : α} (h : decode b = some a) :
    encode a = b := by
  unfold decode at h
  split at h
  · rename_i a' _
    split at h
    · rename_i he
      cases h
      cases b with
      | mk d => simp only [encode, he, Array.toArray_toList]
    · cases h
  · cases h

theorem encode_inj {α} [Codec α] {a b : α} (h : encode a = encode b) : a = b := by
  have := congrArg (decode (α := α)) h
  rw [decode_encode, decode_encode] at this
  exact Option.some.inj this

/-! ## What runs -/

/-- `encode`, as it runs: the value's bytes pushed into a buffer. -/
def encodeFast {α} [Codec α] (a : α) : ByteArray := encInto .empty a

/-- `decode`, as it runs: the value read at offset 0, kept if it ends
at the end of b and encodes to b. -/
def decodeFast {α} [Codec α] (b : ByteArray) : Option α :=
  match (decFrom b 0 : Option (α × Nat)) with
  | some (a, j) => if j = b.size ∧ encodeFast a = b then some a else none
  | none => none

theorem encode_eq_enc {α} [Codec α] {a : α} {b : ByteArray} : encode a = b ↔ enc a = b.data.toList := by
  constructor
  · rintro rfl; simp [encode]
  · intro h; cases b with
    | mk d => simp only [encode, h, Array.toArray_toList]

/-- **`encode` runs as `encodeFast`.** -/
@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext α _ a
  apply ByteArray.ext
  apply Array.toList_inj.1
  simp [encode, encodeFast, encInto_eq]

theorem decode_some {α} [Codec α] {b : ByteArray} {a : α} : decode b = some a ↔ enc a = b.data.toList := by
  constructor
  · intro h; exact encode_eq_enc.1 (encode_decode h)
  · intro h; rw [← encode_eq_enc.2 h]; exact decode_encode a

theorem decodeFast_some {α} [Codec α] {b : ByteArray} {a : α} :
    decodeFast b = some a ↔ enc a = b.data.toList := by
  have hf : ∀ a' : α, encodeFast a' = b ↔ enc a' = b.data.toList := fun a' => by
    rw [← encode_eq_fast]; exact encode_eq_enc
  unfold decodeFast
  constructor
  · intro h
    split at h
    · split at h
      · rename_i hc; cases h; exact (hf _).1 hc.2
      · cases h
    · cases h
  · intro h
    have hat : At b 0 (enc a) := by rw [h]; exact At.whole b
    rw [decFrom_at a hat]
    dsimp only
    rw [ite_eq_left ⟨by simp [h], (hf a).2 h⟩]

/-- **`decode` runs as `decodeFast`**, on every input. -/
@[csimp] theorem decode_eq_fast : @decode = @decodeFast := by
  funext α _ b
  apply Option.ext
  intro a
  rw [decode_some, decodeFast_some]

end Codec

end Engine
