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
-/
namespace Engine

class Codec (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Option (α × List UInt8)
  round : ∀ a rest, dec (enc a ++ rest) = some (a, rest)

namespace Codec

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

instance : Codec Nat := ⟨encNat, decNat, decNat_encNat⟩

def encBytesL (l : List UInt8) : List UInt8 := encNat l.length ++ l

def decBytesL (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match decNat bs with
  | none => none
  | some (n, rest) => if n ≤ rest.length then some (rest.take n, rest.drop n) else none

theorem decBytesL_encBytesL (l rest : List UInt8) : decBytesL (encBytesL l ++ rest) = some (l, rest) := by
  unfold decBytesL encBytesL
  rw [List.append_assoc, decNat_encNat]
  simp

instance : Codec ByteArray where
  enc b := encBytesL b.data.toList
  dec bs := (decBytesL bs).map fun p => (⟨p.1.toArray⟩, p.2)
  round b rest := by
    rw [decBytesL_encBytesL]; simp

instance : Codec Bool where
  enc b := [if b then 1 else 0]
  dec | b :: rest => if b = 1 then some (true, rest) else if b = 0 then some (false, rest) else none
      | [] => none
  round b rest := by cases b <;> rfl

instance : Codec UInt8 where
  enc b := [b]
  dec | b :: rest => some (b, rest)
      | [] => none
  round _ _ := rfl

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

instance {α} [Codec α] : Codec (List α) where
  enc := encList
  dec bs := decListF (bs.length + 1) bs
  round l rest := by
    apply decListF_encList
    have := length_le_encList l
    simp; omega

def decPair {α β} [Codec α] [Codec β] (bs : List UInt8) : Option ((α × β) × List UInt8) :=
  match (dec bs : Option (α × List UInt8)) with
  | none => none
  | some (a, r) => match (dec r : Option (β × List UInt8)) with
    | none => none
    | some (b, r') => some ((a, b), r')

instance {α β} [Codec α] [Codec β] : Codec (α × β) where
  enc p := enc p.1 ++ enc p.2
  dec := decPair
  round p rest := by
    unfold decPair
    rw [List.append_assoc, Codec.round p.1]
    simp only
    rw [Codec.round p.2]

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

theorem length_encNat_pos (n : Nat) : 0 < (encNat n).length := by
  rw [encNat]; split <;> simp

/-- A byte string's encoding is its length, then it. -/
theorem length_enc_bytes (b : ByteArray) : (enc b).length = (encNat b.size).length + b.size := by
  show (encBytesL b.data.toList).length = _
  rw [encBytesL, List.length_append, Array.length_toList]
  rfl

theorem length_encList_bytes (l : List ByteArray) :
    (l.map ByteArray.size).sum + l.length + 1 ≤ (encList l).length := by
  induction l with
  | nil => simp [encList]
  | cons a t ih =>
    rw [encList, List.length_cons, List.length_cons, List.length_append, List.map_cons,
      List.sum_cons, length_enc_bytes]
    have := length_encNat_pos a.size
    omega

/-- **Decoded byte strings are no larger than their bytes:** together,
with a byte each, they are shorter than the list's encoding. -/
theorem decode_sum {b : ByteArray} {l : List ByteArray} (h : decode b = some l) :
    (l.map ByteArray.size).sum + l.length < b.size := by
  rw [← encode_decode h]
  show _ < (encList l).toArray.size
  rw [List.size_toArray]
  have := length_encList_bytes l
  omega

end Codec

end Engine
