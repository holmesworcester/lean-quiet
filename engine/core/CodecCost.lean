/-
What the codec's readers cost, as they run (docs/PERF.md).

A number's reader (`decNatFromM`) and a byte string's (`decBytesFromM`)
run at `Id` as `decNatFrom` and `decBytesFrom`, the `Codec` instances'
`decFrom`. Counted, the same code computes the same thing (`val_*`) and
charges a word operation per byte read alone and per digit joined, and
the bytes it copies in bulk. The budget:
- `work_digitsM`: the digits of an L-byte number, by halves, cost at most
  L·(log₂ L + 2) word operations.
- `work_decNatFromM`: a number read anywhere costs at most
  N·(log₂ N + 3), N the bytes left from where it starts: whatever a
  peer sends, a number is O(N log N).
- `work_decBytesFromM`: a byte string's length costs at most
  log₂|b|/7 + 1 bytes read, whatever the bytes, and its bytes are copied
  once (`cost_decBytesFromM_at`): never read one at a time.

Negative controls, through the same meter:
- `digitsSlowM`, the digits a byte at a time into the number so far, as
  the codec read them before the halves: L·(L+1)/2 work
  (`work_digitsSlowM`), over the budget from 16 bytes on
  (`slow_digits_over_budget`).
- `decBytesListM`, the list codec's way, every byte from the offset on
  read into a list: as many reads as bytes (`work_readAllM`), over the
  budget for any input of two bytes or more (`slow_bytes_over_budget`).

The other codecs (lists, pairs, ops, facts) are not counted: `decFrom`
is a pure field of `Codec`, so a list's reader cannot be charged for its
items' (docs/PERF.md, "Not yet counted").
-/
import engine.core.Codec

namespace Engine.Codec
open Counted

/-! ## Numbers, by halves -/

theorem val_digitsM (b : ByteArray) (L : Nat) :
    ∀ i, val (digitsM (m := Counted) b i L) = digitsFast b i L := by
  induction L using Nat.strongRecOn with
  | _ L ih =>
    intro i
    rw [digitsM, digitsFast_unfold]
    split
    · rfl
    · show val (digitsM (m := Counted) b i (L / 2)) +
          (val (digitsM (m := Counted) b (i + L / 2) (L - L / 2)) <<< (7 * (L / 2))) = _
      rw [ih _ (by omega), ih _ (by omega)]

/-- **The digits of an L-byte number cost L·(k + 1)**, for any k with
L ≤ 2^k: each level of halves joins L digits in all, and there are k
levels. -/
theorem work_digitsM_pow (b : ByteArray) (k : Nat) :
    ∀ L i, L ≤ 2 ^ k → (cost (digitsM (m := Counted) b i L)).work ≤ L * (k + 1) := by
  induction k with
  | zero =>
    intro L i h
    rw [digitsM, ite_eq_left (by simp at h; omega)]
    simp
  | succ k ih =>
    intro L i h
    rw [digitsM]
    split
    · simp only [cost_bind, cost_tick, cost_pure, Meter.add_zero]
      exact Nat.le_mul_of_pos_right L (by omega)
    · rename_i hL
      simp only [cost_bind, cost_tick, cost_pure, Meter.add_zero, Meter.work_add]
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have h1 := ih (L / 2) i (by omega)
      have h2 := ih (L - L / 2) (i + L / 2) (by omega)
      have e : L * (k + 1 + 1) = (L / 2) * (k + 1) + (L - L / 2) * (k + 1) + L := by
        rw [← Nat.add_mul, show L / 2 + (L - L / 2) = L by omega, Nat.mul_succ]
      omega

/-- **An L-byte number's digits cost at most L·(log₂ L + 2)** word
operations. -/
theorem work_digitsM (b : ByteArray) (i L : Nat) :
    (cost (digitsM (m := Counted) b i L)).work ≤ L * (Nat.log2 L + 2) :=
  work_digitsM_pow b _ L i (Nat.le_of_lt Nat.lt_log2_self)

theorem val_numEndM (b : ByteArray) (i : Nat) : val (numEndM (m := Counted) b i) = numEnd b i := by
  induction i using numEndM.induct (b := b) with
  | case1 i h ih =>
    rw [numEndM, dite_eq_left h, numEnd_unfold, dite_eq_left h, val_bind]
    by_cases hlt : b[i].toNat < 128
    · rw [ite_eq_left hlt, ite_eq_left hlt]; rfl
    · rw [ite_eq_right hlt, ite_eq_right hlt]; exact ih
  | case2 i h =>
    rw [numEndM, dite_eq_right h, numEnd_unfold, dite_eq_right h]; rfl

/-- Finding a number's end reads its bytes, one each: at most the bytes
left. -/
theorem work_numEndM (b : ByteArray) (i : Nat) :
    (cost (numEndM (m := Counted) b i)).work ≤ b.size - i := by
  induction i using numEndM.induct (b := b) with
  | case1 i h ih =>
    rw [numEndM, dite_eq_left h, cost_bind, Meter.work_add, cost_tick]
    by_cases hlt : b[i].toNat < 128
    · rw [ite_eq_left hlt]; simp; omega
    · rw [ite_eq_right hlt]; simp only; omega
  | case2 i h =>
    rw [numEndM, dite_eq_right h]; simp

/-- The end it finds is past the offset, inside the bytes, and was found
reading each byte up to it once. -/
theorem numEndM_some (b : ByteArray) (i : Nat) {j : Nat} (h : numEnd b i = some j) :
    i ≤ j ∧ j < b.size ∧ (cost (numEndM (m := Counted) b i)).work = j + 1 - i := by
  induction i using numEndM.induct (b := b) with
  | case1 i h' ih =>
    rw [numEndM, dite_eq_left h', cost_bind, Meter.work_add, cost_tick]
    rw [numEnd_unfold, dite_eq_left h'] at h
    by_cases hlt : b[i].toNat < 128
    · rw [ite_eq_left hlt] at h; cases h
      rw [ite_eq_left hlt]; simp; omega
    · rw [ite_eq_right hlt] at h
      obtain ⟨a, c, d⟩ := ih h
      rw [ite_eq_right hlt]; simp only; omega
  | case2 i h' =>
    rw [numEnd_unfold, dite_eq_right h'] at h; cases h

theorem val_decNatFromM (b : ByteArray) (i : Nat) :
    val (decNatFromM (m := Counted) b i) = decNatFrom b i := by
  rw [decNatFrom_unfold, decNatFromM, val_bind, val_numEndM]
  cases numEnd b i with
  | none => rfl
  | some j => show some (val (digitsM (m := Counted) b i (j + 1 - i)), j + 1) = _; rw [val_digitsM]

theorem log2_mono {a c : Nat} (h : a ≤ c) : Nat.log2 a ≤ Nat.log2 c := by
  by_cases ha : a = 0
  · subst ha; simp [Nat.log2_zero]
  · exact (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le ha) h)

/-- **A number costs O(N log N), whatever the bytes**: at most
N·(log₂ N + 3) word operations, N the bytes from where it starts. -/
theorem work_decNatFromM (b : ByteArray) (i : Nat) :
    (cost (decNatFromM (m := Counted) b i)).work ≤ (b.size - i) * (Nat.log2 (b.size - i) + 3) := by
  rw [decNatFromM, cost_bind, val_numEndM]
  have hn := work_numEndM b i
  cases he : numEnd b i with
  | none =>
    simp only [cost_pure, Meter.add_zero]
    exact Nat.le_trans hn (Nat.le_mul_of_pos_right _ (by omega))
  | some j =>
    obtain ⟨h1, h2, h3⟩ := numEndM_some b i he
    simp only [cost_bind, cost_pure, Meter.add_zero, Meter.work_add]
    have hd := work_digitsM b i (j + 1 - i)
    have hm : (j + 1 - i) * (Nat.log2 (j + 1 - i) + 2) ≤ (b.size - i) * (Nat.log2 (b.size - i) + 2) :=
      Nat.mul_le_mul (by omega) (Nat.add_le_add_right (log2_mono (by omega)) 2)
    have e : (b.size - i) * (Nat.log2 (b.size - i) + 3) =
        (b.size - i) * (Nat.log2 (b.size - i) + 2) + (b.size - i) := by
      rw [show Nat.log2 (b.size - i) + 3 = (Nat.log2 (b.size - i) + 2) + 1 by omega, Nat.mul_succ]
    omega

/-! ### The negative control: a byte at a time -/

/-- The digits read a byte at a time into the number so far, as the
codec did before the halves: each step multiplies the k digits read so
far by 128, charged k + 1. -/
def digitsSlowM {m : Type → Type} [Monad m] [Tick m] (b : ByteArray) (i : Nat) : Nat → m Nat
  | 0 => pure 0
  | L + 1 => do
    let r ← digitsSlowM b (i + 1) L
    tick { work := L + 1 }
    pure (byteAt b i % 128 + 128 * r)

/-- It computes the same digits. -/
theorem val_digitsSlowM (b : ByteArray) : ∀ L i, val (digitsSlowM (m := Counted) b i L) = digits b i L
  | 0, _ => rfl
  | L + 1, i => by
    show byteAt b i % 128 + 128 * val (digitsSlowM (m := Counted) b (i + 1) L) = _
    rw [val_digitsSlowM b L]; rfl

theorem work_digitsSlowM (b : ByteArray) :
    ∀ L i, 2 * (cost (digitsSlowM (m := Counted) b i L)).work = L * (L + 1)
  | 0, _ => rfl
  | L + 1, i => by
    simp only [digitsSlowM, cost_bind, cost_tick, cost_pure, Meter.add_zero, Meter.work_add]
    have := work_digitsSlowM b L (i + 1)
    rw [Nat.mul_add, this]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega

theorem two_pow_ge (t : Nat) (h : 4 ≤ t) : 2 * t + 4 ≤ 2 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [Nat.pow_succ]
    by_cases h4 : t = 3
    · subst h4; decide
    · have := ih (by omega); omega

/-- **The budget catches the byte-at-a-time digits** for every number of
16 bytes or more. -/
theorem slow_digits_over_budget (b : ByteArray) (i L : Nat) (h : 16 ≤ L) :
    L * (Nat.log2 L + 2) < (cost (digitsSlowM (m := Counted) b i L)).work := by
  have hw := work_digitsSlowM b L i
  have ht : 4 ≤ Nat.log2 L := (Nat.le_log2 (by omega)).2 (by simpa using h)
  have hl := Nat.log2_self_le (n := L) (by omega)
  have hp := two_pow_ge _ ht
  -- 2·L·(t + 2) < L·(L + 1), as 2t + 4 < L + 1
  have : L * (2 * (Nat.log2 L + 2)) < L * (L + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  rw [Nat.mul_left_comm] at this
  omega

/-! ## Byte strings: copied once -/

theorem val_decLenFromM (b : ByteArray) (i acc k : Nat) :
    val (decLenFromM (m := Counted) b i acc k) = decLenFrom b i acc k := by
  induction i, acc, k using decLenFromM.induct (b := b) with
  | case1 i acc k h ih =>
    simp only at ih
    rw [decLenFromM, dite_eq_left h, decLenFrom_unfold, dite_eq_left h, val_bind]
    simp only
    by_cases hx : b[i].toNat < 128
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]
      by_cases hs : b.size < k * 128
      · rw [ite_eq_left hs, ite_eq_left hs]; rfl
      · rw [ite_eq_right hs, ite_eq_right hs]; exact ih
  | case2 i acc k h =>
    rw [decLenFromM, dite_eq_right h, decLenFrom_unfold, dite_eq_right h]; rfl

/-- A length goes on only while 128 times its scale still fits in b:
128^(reads − 1) · k ≤ max |b| k. -/
theorem work_decLenFromM (b : ByteArray) (i acc k : Nat) :
    128 ^ ((cost (decLenFromM (m := Counted) b i acc k)).work - 1) * k ≤ max b.size k := by
  induction i, acc, k using decLenFromM.induct (b := b) with
  | case1 i acc k h ih =>
    simp only at ih
    rw [decLenFromM, dite_eq_left h, cost_bind, Meter.work_add, cost_tick]
    simp only
    by_cases hx : b[i].toNat < 128
    · rw [ite_eq_left hx]; simp [Nat.le_max_right]
    · rw [ite_eq_right hx]
      by_cases hs : b.size < k * 128
      · rw [ite_eq_left hs]; simp [Nat.le_max_right]
      · rw [ite_eq_right hs]
        generalize (cost (decLenFromM (m := Counted) b (i + 1) (acc + (b[i].toNat - 128) * k)
          (k * 128))).work = w at ih ⊢
        have hm : max b.size (k * 128) = b.size := Nat.max_eq_left (by omega)
        rw [hm] at ih
        cases w with
        | zero => simp; omega
        | succ w =>
          rw [show 1 + (w + 1) - 1 = w + 1 by omega,
            show 128 ^ (w + 1) * k = 128 ^ w * (k * 128) by
              rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 128 k]]
          simp only [Nat.add_sub_cancel] at ih
          exact Nat.le_trans ih (Nat.le_max_left _ _)
  | case2 i acc k h =>
    rw [decLenFromM, dite_eq_right h]; simp [Nat.le_max_right]

theorem cost_decLenFromM_copied (b : ByteArray) (i acc k : Nat) :
    (cost (decLenFromM (m := Counted) b i acc k)).copied = 0 := by
  induction i, acc, k using decLenFromM.induct (b := b) with
  | case1 i acc k h ih =>
    simp only at ih
    rw [decLenFromM, dite_eq_left h, cost_bind, Meter.copied_add, cost_tick]
    simp only
    by_cases hx : b[i].toNat < 128
    · rw [ite_eq_left hx]; rfl
    · rw [ite_eq_right hx]
      by_cases hs : b.size < k * 128
      · rw [ite_eq_left hs]; rfl
      · rw [ite_eq_right hs, ih]
  | case2 i acc k h =>
    rw [decLenFromM, dite_eq_right h]; rfl

/-- A length read where an encoded one is costs one read per byte of
its encoding. -/
theorem work_decLenFromM_at {b : ByteArray} (n : Nat) : ∀ {i : Nat} (acc k : Nat), At b i (encNat n) →
    acc + n * k ≤ b.size → (cost (decLenFromM (m := Counted) b i acc k)).work = (encNat n).length := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i acc k h hb
    by_cases hn : n < 128
    · rw [encNat_small hn] at h ⊢
      obtain ⟨hi, hx⟩ := h.get
      rw [decLenFromM, dite_eq_left hi, cost_bind, Meter.work_add, cost_tick]
      simp only
      rw [hx, toNat_small hn, ite_eq_left hn]; simp
    · rw [encNat_big hn] at h ⊢
      obtain ⟨hi, hx⟩ := h.get
      have hm : 128 * k ≤ n * k := Nat.mul_le_mul_right k (by omega)
      rw [decLenFromM, dite_eq_left hi, cost_bind, Meter.work_add, cost_tick]
      simp only
      rw [hx, toNat_big, ite_eq_right (by omega), ite_eq_right (by omega),
        ih (n / 128) (by omega) _ _ h.cons (by rw [split128]; exact hb)]
      simp; omega

theorem val_decBytesFromM (b : ByteArray) (i : Nat) :
    val (decBytesFromM (m := Counted) b i) = decBytesFrom b i := by
  rw [decBytesFrom_unfold, decBytesFromM, val_bind, val_decLenFromM]
  rcases decLenFrom b i 0 1 with _ | ⟨n, j⟩
  · rfl
  · show val (if j + n ≤ b.size then _ else _) = (if j + n ≤ b.size then _ else _)
    by_cases h : j + n ≤ b.size <;> simp only [h, ite_true, ite_false] <;> rfl

/-- **A byte string's length costs at most log₂|b|/7 + 1 bytes read,
whatever the bytes.** -/
theorem work_decBytesFromM (b : ByteArray) (i : Nat) :
    (cost (decBytesFromM (m := Counted) b i)).work ≤ Nat.log2 b.size / 7 + 1 := by
  have key : (cost (decBytesFromM (m := Counted) b i)).work =
      (cost (decLenFromM (m := Counted) b i 0 1)).work := by
    rw [decBytesFromM, cost_bind, Meter.work_add]
    rcases val (decLenFromM (m := Counted) b i 0 1) with _ | ⟨n, j⟩
    · rfl
    · show _ + (cost (if j + n ≤ b.size then _ else _)).work = _
      split <;> simp
  rw [key]
  have h := work_decLenFromM b i 0 1
  generalize (cost (decLenFromM (m := Counted) b i 0 1)).work = w at h ⊢
  rw [Nat.mul_one] at h
  cases w with
  | zero => omega
  | succ w =>
    simp only [Nat.add_sub_cancel] at h
    by_cases hb : b.size = 0
    · have h1 : 128 ^ w ≤ 1 := by rw [hb] at h; exact h
      cases w with
      | zero => simp
      | succ w => rw [Nat.pow_succ] at h1; have := Nat.one_le_pow w 128 (by decide); omega
    · rw [Nat.max_eq_left (by omega), show (128 : Nat) = 2 ^ 7 by rfl, ← Nat.pow_mul] at h
      have := (Nat.le_log2 hb).2 h
      omega

/-- **A byte string's bytes are copied once, never read one at a
time**: decoding x reads only its length prefix, and copies x's bytes in
one go. -/
theorem cost_decBytesFromM_at {b : ByteArray} {i : Nat} (x : ByteArray) (h : At b i (enc x)) :
    (cost (decBytesFromM (m := Counted) b i)).work = (encNat x.size).length ∧
      (cost (decBytesFromM (m := Counted) b i)).copied = x.size := by
  have hl : x.data.toList.length = x.size := by simp
  have h' : At b i (encNat x.size ++ x.data.toList) := by
    have : enc x = encBytesL x.data.toList := rfl
    rw [this, encBytesL, hl] at h; exact h
  have hle := h'.length_le
  simp only [List.length_append, Array.length_toList, ByteArray.size_data] at hle
  have hd := decLenFrom_at x.size 0 1 h'.left (by omega)
  simp only [Nat.zero_add, Nat.mul_one] at hd
  have hw := work_decLenFromM_at x.size 0 1 h'.left (by omega)
  have := length_encNat_pos x.size
  rw [decBytesFromM, cost_bind, val_decLenFromM, hd]
  show (cost (decLenFromM (m := Counted) b i 0 1) +
    cost (if i + (encNat x.size).length + x.size ≤ b.size then _ else _)).work = _ ∧
    (cost (decLenFromM (m := Counted) b i 0 1) +
    cost (if i + (encNat x.size).length + x.size ≤ b.size then _ else _)).copied = _
  rw [ite_eq_left (by omega)]
  simp [hw, cost_decLenFromM_copied]

/-! ### The negative control: the list codec's way -/

/-- The bytes from i on, read one at a time into a list, as the list
codec had them (`b.data.toList`). -/
def readAllM {m : Type → Type} [Monad m] [Tick m] (b : ByteArray) (i : Nat) : m (List UInt8) :=
  if h : i < b.size then do
    tick { work := 1 }
    let rest ← readAllM b (i + 1)
    pure (b[i] :: rest)
  else pure []
termination_by b.size - i

/-- A byte string at offset i, the list codec's way: every byte from i
on read into a list, then the list decoded. -/
def decBytesListM {m : Type → Type} [Monad m] [Tick m] (b : ByteArray) (i : Nat) :
    m (Option (ByteArray × Nat)) := do
  let l ← readAllM b i
  pure ((decBytesL l).map fun p => (⟨p.1.toArray⟩, b.size - p.2.length))

/-- It reads the bytes from i on, each once. -/
theorem readAllM_eq (b : ByteArray) (i : Nat) :
    val (readAllM (m := Counted) b i) = b.data.toList.drop i ∧
      (cost (readAllM (m := Counted) b i)).work = b.size - i := by
  induction i using readAllM.induct (b := b) with
  | case1 i h ih =>
    rw [readAllM, dite_eq_left h]
    simp only [val_bind, val_pure, cost_bind, cost_tick, cost_pure, Meter.add_zero,
      Meter.work_add, ih.1, ih.2]
    refine ⟨?_, by omega⟩
    conv => rhs; rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp; rfl
  | case2 i h =>
    rw [readAllM, dite_eq_right h]
    refine ⟨?_, by simp; omega⟩
    rw [val_pure, List.drop_eq_nil_of_le (by simp; omega)]

theorem work_readAllM (b : ByteArray) (i : Nat) :
    (cost (decBytesListM (m := Counted) b i)).work = b.size - i := by
  rw [decBytesListM, cost_bind, cost_pure, Meter.add_zero, (readAllM_eq b i).2]

/-- **The budget catches the list codec's way** on any input of two
bytes or more. -/
theorem slow_bytes_over_budget (b : ByteArray) (h : 2 ≤ b.size) :
    Nat.log2 b.size / 7 + 1 < (cost (decBytesListM (m := Counted) b 0)).work := by
  rw [work_readAllM]
  have := Nat.log2_lt (n := b.size) (by omega) |>.2 (Nat.lt_two_pow_self)
  omega

end Engine.Codec
