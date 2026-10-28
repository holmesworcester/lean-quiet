/-
Bits as lists of `Bool`, most significant first: how a QR symbol's data
stream is written and read. `bitsOf` writes a number in a fixed width;
`readBits` reads one back and returns the bits after it. Reading what
was written gives back the number (`readBits_bitsOf`), and a read always
consumes exactly its width (`readBits_length`).
-/
namespace Qr

/-- The low `k` bits of `n`, most significant first. -/
def bitsOf (n : Nat) : Nat → List Bool
  | 0 => []
  | k + 1 => (n / 2 ^ k % 2 == 1) :: bitsOf n k

/-- Reads a `k`-bit number, most significant bit first, and the bits after
it; `none` if fewer than `k` bits are left. -/
def readBits : Nat → List Bool → Option (Nat × List Bool)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    match readBits k bs with
    | some (v, r) => some ((if b then 2 ^ k else 0) + v, r)
    | none => none

/-- A byte's 8 bits. -/
def byteBits (b : UInt8) : List Bool := bitsOf b.toNat 8

/-- Bytes as bits, each most significant bit first. -/
def bytesBits (bs : List UInt8) : List Bool := bs.flatMap byteBits

/-- The byte of 8 bits. -/
def byteOf (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : UInt8 :=
  let v (b : Bool) (w : Nat) := if b then w else 0
  (v b0 128 + v b1 64 + v b2 32 + v b3 16 + v b4 8 + v b5 4 + v b6 2 + v b7 1).toUInt8

/-- Bits packed into bytes, 8 at a time; a short last group is padded with
zeros. -/
def packBytes : List Bool → List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    byteOf b0 b1 b2 b3 b4 b5 b6 b7 :: packBytes rest
  | [] => []
  | rest =>
    let g (i : Nat) := rest.getD i false
    [byteOf (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)]

@[simp] theorem bitsOf_length (n k : Nat) : (bitsOf n k).length = k := by
  induction k <;> simp [bitsOf, *]

theorem readBits_bitsOf (n k : Nat) (r : List Bool) :
    readBits k (bitsOf n k ++ r) = some (n % 2 ^ k, r) := by
  induction k with
  | zero => simp [bitsOf, readBits, Nat.mod_one]
  | succ k ih =>
    simp only [bitsOf, List.cons_append, readBits, ih, Nat.mod_pow_succ (b := 2)]
    have h2 : n / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases (by omega : n / 2 ^ k % 2 = 0 ∨ n / 2 ^ k % 2 = 1) with h | h <;>
      simp [h] <;> omega

theorem readBits_bitsOf_lt {n k : Nat} (h : n < 2 ^ k) (r : List Bool) :
    readBits k (bitsOf n k ++ r) = some (n, r) := by
  rw [readBits_bitsOf, Nat.mod_eq_of_lt h]

theorem readBits_length {k : Nat} {bs r : List Bool} {v : Nat}
    (h : readBits k bs = some (v, r)) : bs.length = k + r.length := by
  induction k generalizing bs v r with
  | zero => simp [readBits] at h; simp [h]
  | succ k ih =>
    cases bs with
    | nil => simp [readBits] at h
    | cons b bs =>
      simp only [readBits] at h
      split at h
      · rename_i v' r' hr
        simp at h
        have := ih hr
        simp [this, ← h.2]; omega
      · simp at h

theorem readBits_lt {k : Nat} {bs r : List Bool} {v : Nat}
    (h : readBits k bs = some (v, r)) : v < 2 ^ k := by
  induction k generalizing bs v r with
  | zero => simp [readBits] at h; simp [← h.1]
  | succ k ih =>
    cases bs with
    | nil => simp [readBits] at h
    | cons b bs =>
      simp only [readBits] at h
      split at h
      · rename_i v' r' hr
        simp at h
        have := ih hr
        rw [← h.1, Nat.pow_succ]
        split <;> omega
      · simp at h

/-- Reading fewer bits than are left fails. -/
theorem readBits_short {k : Nat} {bs : List Bool} (h : bs.length < k) : readBits k bs = none := by
  induction k generalizing bs with
  | zero => simp at h
  | succ k ih =>
    cases bs with
    | nil => simp [readBits]
    | cons b bs =>
      simp at h
      simp [readBits, ih (by omega)]

theorem byteBits_byteOf (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    byteBits (byteOf b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;>
    cases b7 <;> rfl

theorem bytesBits_append (a b : List UInt8) : bytesBits (a ++ b) = bytesBits a ++ bytesBits b := by
  simp [bytesBits]

/-- Packing whole bytes' worth of bits and unpacking them is the identity. -/
theorem bytesBits_packBytes (bs : List Bool) (h : bs.length % 8 = 0) :
    bytesBits (packBytes bs) = bs := by
  match bs, h with
  | [], _ => rfl
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h =>
    simp only [packBytes, bytesBits, List.flatMap_cons]
    rw [byteBits_byteOf]
    have := bytesBits_packBytes rest (by simp at h; omega)
    simp only [bytesBits] at this
    simp [this]
  | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => simp at h

theorem readBits_none_of_length {bs : List Bool} {k : Nat} (h : readBits k bs = none) :
    bs.length < k := by
  induction k generalizing bs with
  | zero => simp [readBits] at h
  | succ k ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      simp only [readBits] at h
      split at h
      · simp at h
      · rename_i hr
        have := ih hr
        simp; omega

end Qr
