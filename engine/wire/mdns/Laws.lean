/-
The laws of the codec, proven on the code the app runs (`decode`,
`encode`), not on a model of it:

* `decode_encode`: a valid message survives the wire. Encoding it and
  decoding the bytes gives it back, field for field.
* `decode_valid`: whatever the decoder accepts is valid. Each label has 1
  to 63 bytes, each name at most 255 wire bytes however its pointers were
  laid out, A and AAAA addresses have 4 and 16 bytes, TXT strings fit
  their length byte, rdata fits its 16-bit length. Together with the first
  law: any packet decodes to something the encoder can send back.

That the decoder ends on every input, compression pointers included, is
not a theorem here but a fact Lean checks when it accepts `nameAt` (see
Mdns.Decode).
-/
import Mdns.Decode

namespace Mdns

-- Bytes at a position
-- -------------------

/-- `xs` sits in `b` at `i`. -/
def At (b : Array UInt8) (i : Nat) (xs : List UInt8) : Prop :=
  i + xs.length ≤ b.size ∧ ∀ k (h : k < xs.length), b[i + k]? = some xs[k]

theorem At.append {b i xs ys} : At b i (xs ++ ys) ↔ At b i xs ∧ At b (i + xs.length) ys := by
  constructor
  · rintro ⟨hs, h⟩
    simp only [List.length_append] at hs
    refine ⟨⟨by omega, fun k hk => ?_⟩, ⟨by omega, fun k hk => ?_⟩⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (xs.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨⟨h1, ha⟩, ⟨h2, hb⟩⟩
    refine ⟨by simp; omega, fun k hk => ?_⟩
    by_cases hk' : k < xs.length
    · rw [List.getElem_append_left hk']; exact ha k hk'
    · have := hb (k - xs.length) (by simp at hk; omega)
      rw [List.getElem_append_right (by omega)]
      have e : i + xs.length + (k - xs.length) = i + k := by omega
      rwa [e] at this

theorem At.cons {b i x xs} : At b i (x :: xs) ↔ b[i]? = some x ∧ At b (i + 1) xs := by
  have := @At.append b i [x] xs
  simp only [List.singleton_append] at this
  rw [this]
  constructor
  · rintro ⟨⟨_, h⟩, h2⟩
    exact ⟨by simpa using h 0 (by simp), h2⟩
  · rintro ⟨h, h2⟩
    refine ⟨⟨?_, fun k hk => ?_⟩, h2⟩
    · rcases Array.getElem?_eq_some_iff.mp h with ⟨hi, _⟩; simp; omega
    · simp at hk; subst hk; simpa using h

theorem At.extract {b i xs} (h : At b i xs) : (b.extract i (i + xs.length)).toList = xs := by
  rcases h with ⟨hs, h⟩
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    have := h k h2
    rw [Array.getElem?_eq_getElem (by omega)] at this
    simp only [Option.some.injEq] at this
    simp [Array.getElem_toList, Array.getElem_extract, this]

theorem At.cast {b i j xs} (h : At b i xs) (e : i = j) : At b j xs := e ▸ h

theorem At.size {b i xs} (h : At b i xs) : i + xs.length ≤ b.size := h.1

-- Numbers
-- -------

theorem u8_at {b i x} (h : b[i]? = some x) : u8 b i = some (x.toNat, i + 1) := by
  simp [u8, h]

theorem u16_at {b i v} (hv : v < 65536) (h : At b i (be16 v)) : u16 b i = some (v, i + 2) := by
  simp only [be16, At.cons] at h
  rcases h with ⟨h0, h1, -⟩
  simp only [u16, u8_at h0, u8_at h1, bind, Option.bind, pure]
  simp [Nat.toUInt8, UInt8.toNat_ofNat]
  omega

theorem be16_length (v) : (be16 v).length = 2 := rfl
theorem be32_length (v) : (be32 v).length = 4 := rfl

theorem u32_at {b i v} (hv : v < 4294967296) (h : At b i (be32 v)) :
    u32 b i = some (v, i + 4) := by
  simp only [be32, At.append, be16_length] at h
  simp only [u32, u16_at (by omega) h.1, u16_at (by omega) h.2, bind, Option.bind, pure]
  congr 2; omega

theorem u8_lt {b i v j} (h : u8 b i = some (v, j)) : v < 256 ∧ j = i + 1 := by
  unfold u8 at h; split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨UInt8.toNat_lt _, rfl⟩

theorem u16_lt {b i v j} (h : u16 b i = some (v, j)) : v < 65536 ∧ j = i + 2 := by
  simp only [u16, bind, Option.bind] at h
  split at h <;> try simp at h
  rename_i r1 h1
  split at h <;> try simp at h
  rename_i r2 h2
  obtain ⟨rfl, rfl⟩ := h
  have := u8_lt h1; have := u8_lt h2; omega

theorem u32_lt {b i v j} (h : u32 b i = some (v, j)) : v < 4294967296 ∧ j = i + 4 := by
  simp only [u32, bind, Option.bind] at h
  split at h <;> try simp at h
  rename_i r1 h1
  split at h <;> try simp at h
  rename_i r2 h2
  obtain ⟨rfl, rfl⟩ := h
  have := u16_lt h1; have := u16_lt h2; omega

-- Names
-- -----

/-- Wire bytes of a name's labels (its `wireLen` less the root's zero). -/
def wsum (ls : Name) : Nat := (ls.map (·.length + 1)).sum

theorem wireLen_eq (n : Name) : n.wireLen = wsum n + 1 := rfl

theorem encName_cons (l : Label) (ls : Name) :
    encName (l :: ls) = (l.length.toUInt8 :: l) ++ encName ls := by
  simp [encName, encLabel]

theorem encName_length (n : Name) : (encName n).length = n.wireLen := by
  induction n with
  | nil => rfl
  | cons l ls ih =>
    rw [encName_cons]; simp only [List.length_append, List.length_cons, ih]
    simp [Name.wireLen]; omega

theorem toUInt8_toNat {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat]; omega

theorem nameAt_enc {b} : ∀ (ls : Name) (i lim seen : Nat),
    (∀ l ∈ ls, 0 < l.length ∧ l.length < 64) → seen + wsum ls + 1 ≤ 255 →
    At b i (encName ls) → nameAt b i lim seen none = some (ls, i + (encName ls).length)
  | [], i, lim, seen, _, _, h => by
    simp only [encName, List.map_nil, List.flatten_nil, List.nil_append, At.cons] at h
    rw [nameAt]; split
    · next hx => rw [h.1] at hx; cases hx
    · next n hx => rw [h.1] at hx; cases hx; simp [encName]
  | l :: ls, i, lim, seen, hv, hs, h => by
    rw [encName_cons, List.cons_append, At.cons, At.append] at h
    obtain ⟨h0, hl, hr⟩ := h
    have hl' := hv l (by simp)
    have hsz := hr.size
    have hn := toUInt8_toNat (n := l.length) (by omega)
    have hw : wsum (l :: ls) = l.length + 1 + wsum ls := by simp [wsum]
    have ih := nameAt_enc ls (i + 1 + l.length) lim (seen + l.length + 1)
      (fun x hx => hv x (by simp [hx])) (by omega) hr
    rw [nameAt]; split
    · next hx => rw [h0] at hx; cases hx
    next n hx =>
    rw [h0] at hx; cases hx; simp only [hn]
    rw [if_neg (by omega), if_pos (by omega), if_pos ⟨by omega, by omega⟩]
    simp only [ih, hl.extract, encName_cons, List.length_append, List.length_cons]
    congr 2; omega

theorem name_enc {b i} {n : Name} (hv : n.Valid) (h : At b i (encName n)) :
    name b i = some (n, i + (encName n).length) :=
  nameAt_enc n i i 0 hv.1 (by have := hv.2; rw [wireLen_eq] at this; omega) h

-- Rdata
-- -----

theorem encTxt_cons (x : List UInt8) (ss : List (List UInt8)) :
    encTxt (x :: ss) = (x.length.toUInt8 :: x) ++ encTxt ss := by
  simp [encTxt, encLabel]

theorem txtAt_enc {b} : ∀ (ss : List (List UInt8)) (i : Nat), (∀ x ∈ ss, x.length < 256) →
    At b i (encTxt ss) → txtAt b i (i + (encTxt ss).length) = some ss
  | [], i, _, _ => by rw [txtAt]; simp [encTxt]
  | x :: ss, i, hv, h => by
    rw [encTxt_cons, List.cons_append, At.cons, At.append] at h
    obtain ⟨h0, hl, hr⟩ := h
    have hn := toUInt8_toNat (hv x (by simp))
    have ih := txtAt_enc ss (i + 1 + x.length) (fun y hy => hv y (by simp [hy])) hr
    have hsz := hr.size
    have e : i + (encTxt (x :: ss)).length = i + 1 + x.length + (encTxt ss).length := by
      simp [encTxt_cons]; omega
    rw [e, txtAt, dif_pos (by omega)]; split
    · next hx => rw [h0] at hx; cases hx
    next n hx =>
    rw [h0] at hx; cases hx; simp only [hn]
    rw [if_pos ⟨by omega, by omega⟩, ih, hl.extract]

theorem bytes_at {b i xs} (h : At b i xs) : bytes b i xs.length = some (xs, i + xs.length) := by
  unfold bytes; rw [if_pos h.size, h.extract]

theorem u16_toNat_toUInt16 (v : UInt16) : v.toNat.toUInt16 = v := by simp
theorem u32_toNat_toUInt32 (v : UInt32) : v.toNat.toUInt32 = v := by simp

theorem known_toNat {t : UInt16} (h : known t = false) :
    t.toNat ≠ 1 ∧ t.toNat ≠ 28 ∧ t.toNat ≠ 12 ∧ t.toNat ≠ 33 ∧ t.toNat ≠ 16 := by
  have k : ∀ u : UInt16, known u = true → t.toNat ≠ u.toNat := fun u hu e => by
    rw [UInt16.toNat_inj.mp e] at h; simp_all
  exact ⟨k tA rfl, k tAAAA rfl, k tPTR rfl, k tSRV rfl, k tTXT rfl⟩

theorem rdata_enc {b i} {d : RData} (hv : d.Valid) (h : At b i (encRData d)) :
    rdata b d.type.toNat i (i + (encRData d).length) = some d := by
  cases d with
  | a x =>
    simp only [RData.Valid] at hv
    simp only [encRData] at h ⊢
    have hb := bytes_at h; rw [hv] at hb
    simp [rdata, RData.type, tA, hv, hb]
  | aaaa x =>
    simp only [RData.Valid] at hv
    simp only [encRData] at h ⊢
    have hb := bytes_at h; rw [hv] at hb
    simp [rdata, RData.type, tA, tAAAA, hv, hb]
  | ptr n =>
    simp only [RData.Valid] at hv
    simp only [encRData] at h ⊢
    simp [rdata, RData.type, tA, tAAAA, tPTR, name_enc hv h]
  | srv p w port n =>
    simp only [RData.Valid] at hv
    simp only [encRData, At.append, be16_length] at h ⊢
    obtain ⟨⟨⟨hp, hw⟩, hpt⟩, hn⟩ := h
    have e1 := u16_at (UInt16.toNat_lt _) hp
    have e2 := u16_at (UInt16.toNat_lt _) hw
    have e3 := u16_at (UInt16.toNat_lt _) (hpt.cast (j := i + 2 + 2) (by simp [be16_length]))
    have e4 := name_enc hv (hn.cast (j := i + 2 + 2 + 2) (by simp [be16_length]))
    simp [rdata, RData.type, tA, tAAAA, tPTR, tSRV, bind, Option.bind, e1, e2, e3, e4, be16_length]
    omega
  | txt ss =>
    simp only [RData.Valid] at hv
    simp only [encRData] at h ⊢
    simp [rdata, RData.type, tA, tAAAA, tPTR, tSRV, tTXT, txtAt_enc ss i hv h]
  | other t x =>
    simp only [RData.Valid] at hv
    have := known_toNat hv
    simp only [encRData] at h ⊢
    simp [rdata, RData.type, tA, tAAAA, tPTR, tSRV, tTXT, this, bytes_at h]

-- Records and messages
-- --------------------

theorem question_enc {b i} {q : Question} (hv : q.Valid) (h : At b i (encQuestion q)) :
    question b i = some (q, i + (encQuestion q).length) := by
  simp only [encQuestion, At.append] at h
  obtain ⟨⟨hn, ht⟩, hc⟩ := h
  have e1 := name_enc hv hn
  have e2 := u16_at (UInt16.toNat_lt _) ht
  have e3 := u16_at (UInt16.toNat_lt _) (hc.cast (j := i + (encName q.name).length + 2)
    (by simp [be16_length] <;> omega))
  simp [question, bind, Option.bind, e1, e2, e3, encQuestion, be16_length]
  omega

theorem record_enc {b i} {r : Record} (hv : r.Valid) (h : At b i (encRecord r)) :
    record b i = some (r, i + (encRecord r).length) := by
  obtain ⟨hvn, hvd, hlen⟩ := hv
  simp only [encRecord, At.append] at h
  obtain ⟨⟨⟨⟨⟨hn, ht⟩, hc⟩, httl⟩, hl⟩, hd⟩ := h
  have hsz := hd.size
  let n := (encName r.name).length
  have e1 := name_enc hvn hn
  have e2 := u16_at (UInt16.toNat_lt _) ht
  have e3 := u16_at (UInt16.toNat_lt _) (hc.cast (j := i + n + 2) (by simp [n, be16_length] <;> omega))
  have e4 := u32_at (UInt32.toNat_lt _) (httl.cast (j := i + n + 2 + 2)
    (by simp [n, be16_length, be32_length] <;> omega))
  have e5 := u16_at hlen (hl.cast (j := i + n + 2 + 2 + 4)
    (by simp [n, be16_length, be32_length] <;> omega))
  have e6 := rdata_enc hvd (hd.cast (j := i + n + 2 + 2 + 4 + 2)
    (by simp [n, be16_length, be32_length] <;> omega))
  simp only [List.length_append, be16_length, be32_length] at hsz
  simp [record, bind, Option.bind, e1, e2, e3, e4, e5, e6, n, encRecord, be16_length,
    be32_length]
  refine ⟨by omega, ?_⟩
  omega

theorem many_enc {α b} {p : Nat → Option (α × Nat)} {enc : α → List UInt8} {P : α → Prop}
    (hp : ∀ x i, P x → At b i (enc x) → p i = some (x, i + (enc x).length)) :
    ∀ (xs : List α) (i : Nat), (∀ x ∈ xs, P x) → At b i (xs.map enc).flatten →
      many p xs.length i = some (xs, i + ((xs.map enc).flatten).length)
  | [], i, _, _ => by simp [many]
  | x :: xs, i, hv, h => by
    simp only [List.map_cons, List.flatten_cons, At.append] at h
    have e1 := hp x i (hv x (by simp)) h.1
    have e2 := many_enc hp xs _ (fun y hy => hv y (by simp [hy] <;> omega)) h.2
    simp [many, bind, Option.bind, e1, e2]
    omega

/-- **Law 1.** A valid message survives the wire. -/
theorem decode_encode (m : Msg) (hv : m.Valid) : decode (encode m) = some m := by
  obtain ⟨hq, han, hau, had, lq, lan, lau, lad⟩ := hv
  let b := (encMsg m).toArray
  have hb : At b 0 (encMsg m) := ⟨by simp [b], fun k hk => by simp [b, hk]⟩
  simp only [encMsg, At.append, be16_length] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hqs⟩, hans⟩, haus⟩, hads⟩ := hb
  let q := ((m.questions.map encQuestion).flatten).length
  let a := ((m.answers.map encRecord).flatten).length
  let u := ((m.authority.map encRecord).flatten).length
  have e0 := u16_at (UInt16.toNat_lt _) h0
  have e1 := u16_at (UInt16.toNat_lt _) (h1.cast (j := 0 + 2) (by simp [be16_length]))
  have e2 := u16_at lq (h2.cast (j := 0 + 2 + 2) (by simp [be16_length] <;> omega))
  have e3 := u16_at lan (h3.cast (j := 0 + 2 + 2 + 2) (by simp [be16_length] <;> omega))
  have e4 := u16_at lau (h4.cast (j := 0 + 2 + 2 + 2 + 2) (by simp [be16_length] <;> omega))
  have e5 := u16_at lad (h5.cast (j := 0 + 2 + 2 + 2 + 2 + 2) (by simp [be16_length] <;> omega))
  have f1 := many_enc (fun x i hx h => question_enc (b := b) hx h) _ _ hq
    (hqs.cast (j := 0 + 2 + 2 + 2 + 2 + 2 + 2) (by simp [be16_length] <;> omega))
  have f2 := many_enc (fun x i hx h => record_enc (b := b) hx h) _ _ han
    (hans.cast (j := 0 + 2 + 2 + 2 + 2 + 2 + 2 + q) (by simp [q, be16_length] <;> omega))
  have f3 := many_enc (fun x i hx h => record_enc (b := b) hx h) _ _ hau
    (haus.cast (j := 0 + 2 + 2 + 2 + 2 + 2 + 2 + q + a) (by simp [q, a, be16_length] <;> omega))
  have f4 := many_enc (fun x i hx h => record_enc (b := b) hx h) _ _ had
    (hads.cast (j := 0 + 2 + 2 + 2 + 2 + 2 + 2 + q + a + u) (by simp [q, a, u, be16_length] <;> omega))
  show msgAt b = some m
  simp only [q, a, u] at f2 f3 f4
  simp only [msgAt, bind, Option.bind, e0, e1, e2, e3, e4, e5, f1, f2, f3, f4]
  rw [if_pos (by simp [b, encMsg, be16_length]; omega)]
  simp

-- What the decoder accepts
-- ------------------------

theorem extract_length {b : Array UInt8} {i n : Nat} (h : i + n ≤ b.size) :
    (b.extract i (i + n)).toList.length = n := by
  simp; omega

theorem take_drop_length {b : Array UInt8} {i n : Nat} (h : i + n ≤ b.size) :
    (List.take n (List.drop i b.toList)).length = n := by
  simp; omega

theorem nameAt_valid {b} (pos lim seen : Nat) (fin : Option Nat) {ls : Name} {e : Nat}
    (h : nameAt b pos lim seen fin = some (ls, e)) (hs : seen ≤ 254) :
    (∀ l ∈ ls, 0 < l.length ∧ l.length < 64) ∧ seen + wsum ls + 1 ≤ 255 := by
  rw [nameAt] at h
  split at h
  · simp at h
  next n hx =>
  have hpos : pos < b.size := (Array.getElem?_eq_some_iff.mp hx).1
  split at h
  · simp at h; obtain ⟨rfl, -⟩ := h; simp [wsum]; omega
  split at h
  · split at h
    · next hc =>
      split at h
      · next ls' e' hr =>
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have ih := nameAt_valid (pos + 1 + n.toNat) lim (seen + n.toNat + 1) fin hr (by omega)
        have hl := take_drop_length (b := b) (i := pos + 1) (n := n.toNat) hc.2
        refine ⟨?_, ?_⟩
        · intro l hl'
          simp only [List.mem_cons] at hl'
          rcases hl' with rfl | hl'
          · rw [hl]; omega
          · exact ih.1 l hl'
        · have := ih.2; simp only [wsum, List.map_cons, List.sum_cons] at this ⊢; rw [hl]; omega
      · simp at h
    · simp at h
  · split at h
    · split at h
      · simp at h
      · next m _ =>
        simp only at h
        split at h
        · next hp => exact nameAt_valid _ _ seen _ h hs
        · simp at h
    · simp at h
termination_by (lim, b.size - pos)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by omega)
    | exact Prod.Lex.left _ _ (by omega)

theorem name_valid {b i n j} (h : name b i = some (n, j)) : n.Valid := by
  have := nameAt_valid i i 0 none h (by omega)
  exact ⟨this.1, by rw [wireLen_eq]; omega⟩

theorem bytes_ok {b i n xs j} (h : bytes b i n = some (xs, j)) : xs.length = n ∧ j = i + n := by
  unfold bytes at h; split at h
  · next hc =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨extract_length hc, rfl⟩
  · simp at h

theorem txtAt_valid {b} (i e : Nat) {ss} (h : txtAt b i e = some ss) :
    (∀ x ∈ ss, x.length < 256) ∧ (encTxt ss).length = e - i ∧ i ≤ e := by
  rw [txtAt] at h
  split at h
  · split at h
    · simp at h
    · next n hx =>
      split at h
      · next hc =>
        split at h
        · next ss' hr =>
          simp at h; subst h
          have ih := txtAt_valid (i + 1 + n.toNat) e hr
          have hl := take_drop_length (b := b) (i := i + 1) (n := n.toNat) (by omega)
          refine ⟨?_, ?_, by omega⟩
          · intro x hx'
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · rw [hl]; exact UInt8.toNat_lt _
            · exact ih.1 x hx'
          · rw [encTxt_cons]; simp only [List.length_append, List.length_cons, hl, ih.2]
            have := UInt8.toNat_lt n
            omega
        · simp at h
      · simp at h
  · split at h
    · simp at h; subst h; simp [encTxt]; omega
    · simp at h
termination_by e - i

theorem known_ofNat {t : Nat} (ht : t < 65536)
    (h : ¬t = 1 ∧ ¬t = 28 ∧ ¬t = 12 ∧ ¬t = 33 ∧ ¬t = 16) : known t.toUInt16 = false := by
  have k : ∀ u : UInt16, t.toUInt16 = u → t = u.toNat := fun u e => by
    rw [← e]; simp; omega
  simp only [known, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨fun e => ?_, fun e => ?_⟩, fun e => ?_⟩, fun e => ?_⟩, fun e => ?_⟩
  · exact h.1 (k _ e)
  · exact h.2.2.1 (k _ e)
  · exact h.2.2.2.2 (k _ e)
  · exact h.2.1 (k _ e)
  · exact h.2.2.2.1 (k _ e)

theorem rdata_valid {b t i e d} (h : rdata b t i e = some d) (hl : e - i < 65536)
    (ht : t < 65536) : d.Valid ∧ (encRData d).length < 65536 := by
  unfold rdata at h
  split at h
  · split at h
    · cases hb : bytes b i 4 with
      | none => simp [hb] at h
      | some r => simp [hb] at h; subst h; have := bytes_ok hb; simp [RData.Valid, encRData, this.1]
    · simp at h
  split at h
  · split at h
    · cases hb : bytes b i 16 with
      | none => simp [hb] at h
      | some r => simp [hb] at h; subst h; have := bytes_ok hb; simp [RData.Valid, encRData, this.1]
    · simp at h
  split at h
  · split at h
    · next n j hn =>
      split at h
      · simp at h; subst h
        have hv := name_valid hn
        refine ⟨hv, ?_⟩; simp only [encRData, encName_length]; have := hv.2; omega
      · simp at h
    · simp at h
  split at h
  · simp only [bind, Option.bind] at h
    rcases h1 : u16 b i with _ | ⟨p, j1⟩
    · simp [h1] at h
    simp only [h1] at h
    rcases h2 : u16 b j1 with _ | ⟨w, j2⟩
    · simp [h2] at h
    simp only [h2] at h
    rcases h3 : u16 b j2 with _ | ⟨pt, j3⟩
    · simp [h3] at h
    simp only [h3] at h
    rcases hn : name b j3 with _ | ⟨n, j4⟩
    · simp [hn] at h
    simp only [hn] at h
    split at h
    · simp at h; subst h
      have hv := name_valid hn
      refine ⟨hv, ?_⟩; simp only [encRData, encName_length, List.length_append, be16_length]
      have := hv.2; omega
    · simp at h
  split at h
  · cases ht' : txtAt b i e with
    | none => simp [ht'] at h
    | some ss =>
      simp [ht'] at h; subst h
      have := txtAt_valid i e ht'
      exact ⟨this.1, by simp only [encRData]; omega⟩
  · cases hb : bytes b i (e - i) with
    | none => simp [hb] at h
    | some r =>
      simp [hb] at h; subst h
      have := bytes_ok hb
      refine ⟨known_ofNat ht (by simp_all [tA, tAAAA, tPTR, tSRV, tTXT]), ?_⟩
      simp only [encRData]; omega

theorem question_valid {b i q j} (h : question b i = some (q, j)) : q.Valid := by
  simp only [question, bind, Option.bind] at h
  rcases hn : name b i with _ | ⟨n, j1⟩
  · simp [hn] at h
  simp only [hn] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  obtain ⟨rfl, -⟩ := h
  exact name_valid hn

theorem record_valid {b i r j} (h : record b i = some (r, j)) : r.Valid := by
  simp only [record, bind, Option.bind] at h
  rcases hn : name b i with _ | ⟨n, j1⟩
  · simp [hn] at h
  simp only [hn] at h
  rcases ht : u16 b j1 with _ | ⟨t, j2⟩
  · simp [ht] at h
  simp only [ht] at h
  rcases hc : u16 b j2 with _ | ⟨c, j3⟩
  · simp [hc] at h
  simp only [hc] at h
  rcases httl : u32 b j3 with _ | ⟨ttl, j4⟩
  · simp [httl] at h
  simp only [httl] at h
  rcases hl : u16 b j4 with _ | ⟨len, j5⟩
  · simp [hl] at h
  simp only [hl] at h
  split at h
  · rcases hd : rdata b t j5 (j5 + len) with _ | d
    · simp [hd] at h
    simp only [hd] at h
    simp at h; obtain ⟨rfl, -⟩ := h
    have := rdata_valid hd (by have := (u16_lt hl).1; omega) (u16_lt ht).1
    exact ⟨name_valid hn, this⟩
  · simp at h

theorem many_valid {α} {p : Nat → Option (α × Nat)} {P : α → Prop}
    (hp : ∀ i x j, p i = some (x, j) → P x) :
    ∀ (k i : Nat) {xs j}, many p k i = some (xs, j) → (∀ x ∈ xs, P x) ∧ xs.length = k
  | 0, i, xs, j, h => by simp [many] at h; obtain ⟨rfl, -⟩ := h; simp
  | k + 1, i, xs, j, h => by
    simp only [many, bind, Option.bind] at h
    rcases h1 : p i with _ | ⟨x, i1⟩
    · simp [h1] at h
    simp only [h1] at h
    rcases h2 : many p k i1 with _ | ⟨ys, i2⟩
    · simp [h2] at h
    simp only [h2] at h
    simp at h; obtain ⟨rfl, -⟩ := h
    have ih := many_valid hp k i1 h2
    refine ⟨?_, by simp [ih.2]⟩
    intro y hy; simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hp _ _ _ h1
    · exact ih.1 y hy

/-- **Law 2.** Whatever the decoder accepts is a valid message. -/
theorem decode_valid {p : ByteArray} {m : Msg} (h : decode p = some m) : m.Valid := by
  simp only [decode, msgAt, bind, Option.bind] at h
  rcases h0 : u16 p.data 0 with _ | ⟨_, i0⟩
  · simp [h0] at h
  simp only [h0] at h
  rcases h1 : u16 p.data i0 with _ | ⟨_, i1⟩
  · simp [h1] at h
  simp only [h1] at h
  rcases h2 : u16 p.data i1 with _ | ⟨nq, i2⟩
  · simp [h2] at h
  simp only [h2] at h
  rcases h3 : u16 p.data i2 with _ | ⟨na, i3⟩
  · simp [h3] at h
  simp only [h3] at h
  rcases h4 : u16 p.data i3 with _ | ⟨ns, i4⟩
  · simp [h4] at h
  simp only [h4] at h
  rcases h5 : u16 p.data i4 with _ | ⟨nr, i5⟩
  · simp [h5] at h
  simp only [h5] at h
  rcases f1 : many (question p.data) nq i5 with _ | ⟨qs, j1⟩
  · simp [f1] at h
  simp only [f1] at h
  rcases f2 : many (record p.data) na j1 with _ | ⟨an, j2⟩
  · simp [f2] at h
  simp only [f2] at h
  rcases f3 : many (record p.data) ns j2 with _ | ⟨au, j3⟩
  · simp [f3] at h
  simp only [f3] at h
  rcases f4 : many (record p.data) nr j3 with _ | ⟨ad, j4⟩
  · simp [f4] at h
  simp only [f4] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    have g1 := many_valid (fun _ _ _ hq => question_valid hq) _ _ f1
    have g2 := many_valid (fun _ _ _ hr => record_valid hr) _ _ f2
    have g3 := many_valid (fun _ _ _ hr => record_valid hr) _ _ f3
    have g4 := many_valid (fun _ _ _ hr => record_valid hr) _ _ f4
    have := (u16_lt h2).1; have := (u16_lt h3).1; have := (u16_lt h4).1; have := (u16_lt h5).1
    exact ⟨g1.1, g2.1, g3.1, g4.1, by simp only; omega, by simp only; omega,
      by simp only; omega, by simp only; omega⟩
  · simp at h

/-- The laws together: a packet decodes iff to a message that the encoder
sends back as a packet decoding to the same message. -/
theorem decode_roundtrip {p : ByteArray} {m : Msg} (h : decode p = some m) :
    decode (encode m) = some m :=
  decode_encode m (decode_valid h)

end Mdns
