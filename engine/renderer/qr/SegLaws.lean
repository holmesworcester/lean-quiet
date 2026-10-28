/-
The data stream's laws, on the functions the decoder runs:

- `parse_segsBits`: valid segments, followed by a terminator (or by fewer
  than four bits), read back as themselves.
- `parse_dataStream`: the data codewords the encoder makes for valid
  segments parse back to those segments.
- `parse_valid`: whatever `parse` returns is valid, so it can be written
  back (`dataStream`) and read again.
-/
import Qr.Segment

namespace Qr

theorem bitsOf_succ (n k : Nat) : bitsOf n (k + 1) = (n / 2 ^ k % 2 == 1) :: bitsOf n k := rfl

theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_toUInt8 (c : UInt8) : c.toNat.toUInt8 = c := UInt8.ofNat_toNat

theorem dig_dv {c : UInt8} (h : isDigit c = true) : dig (dv c) = c := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [dig, dv, show c.toNat - 48 + 48 = c.toNat by omega, toNat_toUInt8]

theorem dv_lt {c : UInt8} (h : isDigit c = true) : dv c < 10 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [dv]; omega

theorem isDigit_dig {x : Nat} (h : x < 10) : isDigit (dig x) = true := by
  simp only [isDigit, dig, toUInt8_toNat_of_lt (show x + 48 < 256 by omega)]
  simp; omega

theorem alnum_table : ∀ n, n < 256 →
    (match alnumIdx n.toUInt8 with
     | some i => decide (i < 45) && alnumChr i == n.toUInt8
     | none => true) = true := by
  decide +kernel

theorem alnum_chr_table : ∀ i, i < 45 → (alnumIdx (alnumChr i)).isSome = true := by
  decide +kernel

theorem alnumChr_av {c : UInt8} (h : (alnumIdx c).isSome = true) :
    av c < 45 ∧ alnumChr (av c) = c := by
  have t := alnum_table c.toNat c.toNat_lt
  rw [toNat_toUInt8] at t
  simp only [av]
  cases hc : alnumIdx c with
  | none => simp [hc] at h
  | some i => simp [hc] at t; simpa using t

theorem readNum_numBits : ∀ (ds : List UInt8) (r : List Bool), (∀ d ∈ ds, isDigit d = true) →
    readNum ds.length (numBits ds ++ r) = some (ds, r)
  | [], r, _ => rfl
  | [a], r, h => by
    have ha := h a (by simp)
    have := dv_lt ha
    simp [numBits, readNum, readBits_bitsOf_lt (show dv a < 2 ^ 4 by omega), this, dig_dv ha]
  | [a, b], r, h => by
    have ha := h a (by simp); have hb := h b (by simp)
    have := dv_lt ha; have := dv_lt hb
    simp only [List.length_cons, List.length_nil, numBits, readNum]
    rw [readBits_bitsOf_lt (show 10 * dv a + dv b < 2 ^ 7 by omega)]
    simp only [show 10 * dv a + dv b < 100 by omega, if_true,
      show (10 * dv a + dv b) / 10 = dv a by omega, show (10 * dv a + dv b) % 10 = dv b by omega,
      dig_dv ha, dig_dv hb]
  | a :: b :: c :: ds, r, h => by
    have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
    have := dv_lt ha; have := dv_lt hb; have := dv_lt hc
    have ih := readNum_numBits ds r (fun d hd => h d (by simp [hd]))
    simp only [List.length_cons, numBits, List.append_assoc]
    rw [show ds.length + 1 + 1 + 1 = ds.length + 3 by omega]
    simp only [readNum]
    rw [readBits_bitsOf_lt (show 100 * dv a + 10 * dv b + dv c < 2 ^ 10 by omega)]
    simp only [show 100 * dv a + 10 * dv b + dv c < 1000 by omega, if_true, ih,
      show (100 * dv a + 10 * dv b + dv c) / 100 = dv a by omega,
      show (100 * dv a + 10 * dv b + dv c) / 10 % 10 = dv b by omega,
      show (100 * dv a + 10 * dv b + dv c) % 10 = dv c by omega,
      dig_dv ha, dig_dv hb, dig_dv hc]

theorem readAlnum_alnumBits : ∀ (cs : List UInt8) (r : List Bool),
    (∀ c ∈ cs, (alnumIdx c).isSome = true) →
    readAlnum cs.length (alnumBits cs ++ r) = some (cs, r)
  | [], r, _ => rfl
  | [a], r, h => by
    have ⟨ha, ea⟩ := alnumChr_av (h a (by simp))
    simp [alnumBits, readAlnum, readBits_bitsOf_lt (show av a < 2 ^ 6 by omega), ha, ea]
  | a :: b :: cs, r, h => by
    have ⟨ha, ea⟩ := alnumChr_av (h a (by simp))
    have ⟨hb, eb⟩ := alnumChr_av (h b (by simp))
    have ih := readAlnum_alnumBits cs r (fun d hd => h d (by simp [hd]))
    simp only [List.length_cons, alnumBits, List.append_assoc]
    rw [show cs.length + 1 + 1 = cs.length + 2 by omega]
    simp only [readAlnum]
    rw [readBits_bitsOf_lt (show 45 * av a + av b < 2 ^ 11 by omega)]
    simp only [show 45 * av a + av b < 2025 by omega, if_true, ih,
      show (45 * av a + av b) / 45 = av a by omega, show (45 * av a + av b) % 45 = av b by omega,
      ea, eb]

theorem readBytes_bytesBits : ∀ (bs : List UInt8) (r : List Bool),
    readBytes bs.length (bytesBits bs ++ r) = some (bs, r)
  | [], r => rfl
  | b :: bs, r => by
    simp only [List.length_cons, bytesBits, List.flatMap_cons, List.append_assoc, readBytes,
      byteBits]
    rw [readBits_bitsOf_lt b.toNat_lt]
    have ih := readBytes_bytesBits bs r
    simp only [bytesBits] at ih
    simp [ih, toNat_toUInt8]

theorem readEci_eciBits {n : Nat} (h : n < 1000000) (r : List Bool) :
    readEci (eciBits n ++ r) = some (n, r) := by
  unfold eciBits
  split
  · simp [readEci, readBits_bitsOf_lt (show n < 2 ^ 7 by omega)]
  · split
    · simp [readEci, readBits_bitsOf_lt (show n < 2 ^ 14 by omega)]
    · simp [readEci, readBits_bitsOf_lt (show n < 2 ^ 21 by omega), h]

theorem readSeg_body {v : Nat} {s : Seg} (hs : s.Valid v) (r : List Bool) :
    readSeg v s.mode (s.body v ++ r) = some (s, r) := by
  cases s with
  | numeric ds =>
    simp only [Seg.Valid] at hs
    simp only [Seg.mode, Seg.body, readSeg, List.append_assoc, readBits_bitsOf_lt hs.1,
      readNum_numBits ds r hs.2]
  | alnum cs =>
    simp only [Seg.Valid] at hs
    simp only [Seg.mode, Seg.body, readSeg, List.append_assoc, readBits_bitsOf_lt hs.1,
      readAlnum_alnumBits cs r hs.2]
  | bytes bs =>
    simp only [Seg.Valid] at hs
    simp only [Seg.mode, Seg.body, readSeg, List.append_assoc, readBits_bitsOf_lt hs,
      readBytes_bytesBits bs r]
  | eci n =>
    simp only [Seg.Valid] at hs
    simp only [Seg.mode, Seg.body, readSeg, readEci_eciBits hs r]

theorem mode_lt (s : Seg) : s.mode < 2 ^ 4 := by cases s <;> simp [Seg.mode]
theorem mode_ne (s : Seg) : s.mode ≠ 0 := by cases s <;> simp [Seg.mode]

/-- What may follow the last segment: the terminator, or fewer than four
bits. -/
def Ended (t : List Bool) : Prop := t.length < 4 ∨ ∃ t', t = false :: false :: false :: false :: t'

theorem parse_ended {v : Nat} {t : List Bool} (h : Ended t) : parse v t = some [] := by
  rcases h with h | ⟨t', rfl⟩
  · rw [parse]; split
    · rfl
    · rename_i hr; have := readBits_length hr; omega
  · rw [parse]; split
    · rfl
    · rename_i m r hr
      simp [readBits] at hr
      simp [← hr.1]

/-- **Round trip.** Valid segments followed by a terminator read back as
themselves. -/
theorem parse_segsBits {v : Nat} :
    ∀ (ss : List Seg) (t : List Bool), (∀ s ∈ ss, s.Valid v) → Ended t →
    parse v (segsBits v ss ++ t) = some ss
  | [], t, _, ht => parse_ended ht
  | s :: ss, t, hv, ht => by
    have ih := parse_segsBits ss t (fun x hx => hv x (by simp [hx])) ht
    have hb := readSeg_body (hv s (by simp)) (segsBits v ss ++ t)
    simp only [segsBits, List.flatMap_cons, Seg.bits, List.append_assoc] at ih ⊢
    rw [parse]
    split
    · rename_i hr; rw [readBits_bitsOf_lt (mode_lt s)] at hr; simp at hr
    · rename_i m r hr
      rw [readBits_bitsOf_lt (mode_lt s)] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [mode_ne s, ite_false]
      split
      · rename_i hn; simp only [segsBits] at hb; rw [hb] at hn; simp at hn
      · rename_i s' r' hn
        simp only [segsBits] at hb
        rw [hb] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        simp [ih]

theorem length_padBytes (n : Nat) : (padBytes n).length = n := by simp [padBytes]

theorem length_bytesBits : ∀ (l : List UInt8), (bytesBits l).length = 8 * l.length
  | [] => rfl
  | b :: l => by
    have := length_bytesBits l
    simp only [bytesBits, List.flatMap_cons, List.length_append] at this ⊢
    simp [byteBits, this]; omega

/-- **Round trip, codewords.** The data codewords the encoder makes for
valid segments parse back to them. -/
theorem parse_dataStream {v cap : Nat} {ss : List Seg} {cw : List UInt8}
    (hv : ∀ s ∈ ss, s.Valid v) (h : dataStream v cap ss = some cw) :
    parse v (bytesBits cw) = some ss := by
  simp only [dataStream] at h
  split at h
  · rename_i hfit
    simp only [Option.some.injEq] at h
    subst h
    rw [bytesBits_append, bytesBits_packBytes _ (by simp; omega)]
    simp only [List.append_assoc]
    apply parse_segsBits ss _ hv
    by_cases h4 : 4 ≤ 8 * cap - (segsBits v ss).length
    · right
      rw [show min 4 (8 * cap - (segsBits v ss).length) = 4 by omega]
      exact ⟨_, rfl⟩
    · left
      simp only [List.length_append, List.length_replicate, length_bytesBits, length_padBytes]
      omega
  · simp at h

theorem dig_lt {x : Nat} (h : x < 10) : isDigit (dig x) = true := isDigit_dig h

theorem readNum_valid : ∀ {n : Nat} {bs r : List Bool} {ds : List UInt8},
    readNum n bs = some (ds, r) → ds.length = n ∧ ∀ d ∈ ds, isDigit d = true
  | 0, bs, r, ds, h => by simp [readNum] at h; obtain ⟨rfl, -⟩ := h; simp
  | 1, bs, r, ds, h => by
    simp only [readNum] at h; split at h
    · rename_i x r' hr; split at h
      · rename_i hx; simp at h; obtain ⟨rfl, -⟩ := h; simp [isDigit_dig hx]
      · simp at h
    · simp at h
  | 2, bs, r, ds, h => by
    simp only [readNum] at h; split at h
    · rename_i x r' hr; split at h
      · rename_i hx; simp at h; obtain ⟨rfl, -⟩ := h
        simp [isDigit_dig (show x / 10 < 10 by omega), isDigit_dig (show x % 10 < 10 by omega)]
      · simp at h
    · simp at h
  | n + 3, bs, r, ds, h => by
    simp only [readNum] at h; split at h
    · rename_i x r' hr; split at h
      · rename_i hx; split at h
        · rename_i ds' r'' hn
          simp at h; obtain ⟨rfl, -⟩ := h
          have ih := readNum_valid hn
          refine ⟨by simp [ih.1], ?_⟩
          intro d hd
          simp at hd
          rcases hd with rfl | rfl | rfl | hd
          · exact isDigit_dig (by omega)
          · exact isDigit_dig (by omega)
          · exact isDigit_dig (by omega)
          · exact ih.2 d hd
        · simp at h
      · simp at h
    · simp at h

theorem readAlnum_valid : ∀ {n : Nat} {bs r : List Bool} {cs : List UInt8},
    readAlnum n bs = some (cs, r) → cs.length = n ∧ ∀ c ∈ cs, (alnumIdx c).isSome = true
  | 0, bs, r, cs, h => by simp [readAlnum] at h; obtain ⟨rfl, -⟩ := h; simp
  | 1, bs, r, cs, h => by
    simp only [readAlnum] at h; split at h
    · rename_i x r' hr; split at h
      · rename_i hx; simp at h; obtain ⟨rfl, -⟩ := h; simp [alnum_chr_table x hx]
      · simp at h
    · simp at h
  | n + 2, bs, r, cs, h => by
    simp only [readAlnum] at h; split at h
    · rename_i x r' hr; split at h
      · rename_i hx; split at h
        · rename_i cs' r'' hn
          simp at h; obtain ⟨rfl, -⟩ := h
          have ih := readAlnum_valid hn
          refine ⟨by simp [ih.1], ?_⟩
          intro d hd
          simp at hd
          rcases hd with rfl | rfl | hd
          · exact alnum_chr_table _ (by omega)
          · exact alnum_chr_table _ (by omega)
          · exact ih.2 d hd
        · simp at h
      · simp at h
    · simp at h

theorem readBytes_valid : ∀ {n : Nat} {bs r : List Bool} {cs : List UInt8},
    readBytes n bs = some (cs, r) → cs.length = n
  | 0, bs, r, cs, h => by simp [readBytes] at h; simp [← h.1]
  | n + 1, bs, r, cs, h => by
    simp only [readBytes] at h; split at h
    · rename_i x r' hr; split at h
      · rename_i cs' r'' hn
        simp at h; obtain ⟨rfl, -⟩ := h
        simp [readBytes_valid hn]
      · simp at h
    · simp at h

theorem readEci_valid {bs r : List Bool} {n : Nat} (h : readEci bs = some (n, r)) :
    n < 1000000 := by
  unfold readEci at h
  split at h
  · have := readBits_lt h; omega
  · have := readBits_lt h; omega
  · split at h
    · rename_i x r' hr; split at h
      · rename_i hx; simp at h; omega
      · simp at h
    · simp at h
  · simp at h

theorem readSeg_valid {v m : Nat} {bs r : List Bool} {s : Seg}
    (h : readSeg v m bs = some (s, r)) : s.Valid v := by
  unfold readSeg at h
  split at h
  · split at h
    · rename_i n r' hr; split at h
      · rename_i ds r'' hn; simp at h; obtain ⟨rfl, -⟩ := h
        have := readNum_valid hn; have := readBits_lt hr
        exact ⟨by omega, (readNum_valid hn).2⟩
      · simp at h
    · simp at h
  · split at h
    · rename_i n r' hr; split at h
      · rename_i ds r'' hn; simp at h; obtain ⟨rfl, -⟩ := h
        have := readAlnum_valid hn; have := readBits_lt hr
        exact ⟨by omega, (readAlnum_valid hn).2⟩
      · simp at h
    · simp at h
  · split at h
    · rename_i n r' hr; split at h
      · rename_i ds r'' hn; simp at h; obtain ⟨rfl, -⟩ := h
        have := readBytes_valid hn; have := readBits_lt hr
        show ds.length < _
        omega
      · simp at h
    · simp at h
  · split at h
    · rename_i n r' hr; simp at h; obtain ⟨rfl, -⟩ := h
      exact readEci_valid hr
    · simp at h
  · simp at h

/-- **Soundness.** Every segment `parse` returns is valid. -/
theorem parse_valid {v : Nat} (n : Nat) : ∀ (bs : List Bool), bs.length = n →
    ∀ {ss : List Seg}, parse v bs = some ss → ∀ s ∈ ss, s.Valid v := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bs hn ss h
    rw [parse] at h
    split at h
    · simp at h; subst h; simp
    · rename_i m r hr
      split at h
      · simp at h; subst h; simp
      · split at h
        · simp at h
        · rename_i s r' hs
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ss', hp, rfl⟩ := h
          have := readBits_length hr
          have := readSeg_length hs
          have ih' := ih r'.length (by omega) r' rfl hp
          intro x hx
          simp at hx
          rcases hx with rfl | hx
          · exact readSeg_valid hs
          · exact ih' x hx

end Qr
