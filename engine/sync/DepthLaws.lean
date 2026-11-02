/-
How many messages a round takes on any path, proven of `exchange` (the
two sides' `answer`s composed, RoundLaws.lean).

- `Ends n X Y c`: every path of the round from claim c, which X
  answers, ends within n answers. Once it does, more fuel changes
  nothing (`ends_exchange`).
- **A cut leaves each piece at most ⌈count/fan⌉ of the cutter's items**
  (`piece_size`): the cuts are every `runLen`-th item of a sorted list.
- **Messages per path** (`ends_log`): when each side holds at most
  leaf·fanᵏ items in the claim's range, every path ends within 2k + 2
  answers. The two sides cut in turn, so each side's count drops by
  `fan` every two answers, and a side holding at most `leaf` lists its
  ids. A round over n items therefore takes at most 2k + 2 answers on
  any path, k = ⌈log_fan (n / leaf)⌉, so 2k + 3 messages with the
  opening. That it is then complete is `exchange_log` (TreeLaws.lean).
-/
import engine.sync.RoundLaws

namespace Engine.Sync

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- Every path of the round from claim c, which X answers, ends within n
answers. -/
def Ends : Nat → List α → List α → Claim → Prop
  | 0, _, _, _ => False
  | n + 1, X, Y, c => ∀ c', Out.claim c' ∈ answer key ident h P X c → Ends n Y X c'

end

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

theorem ends_fold_congr (s1 s2 : Claim → List ByteArray × List ByteArray) (os : List Out)
    (hs : ∀ c, Out.claim c ∈ os → s1 c = s2 c) :
    os.foldr (fun o acc => (give s1 o ++ acc.1, get s1 o ++ acc.2)) ([], []) =
      os.foldr (fun o acc => (give s2 o ++ acc.1, get s2 o ++ acc.2)) ([], []) := by
  induction os with
  | nil => rfl
  | cons o t ih =>
    simp only [List.foldr_cons]
    rw [ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))]
    cases o with
    | claim c => simp [give, get, hs c (List.mem_cons_self ..)]
    | hold _ => rfl
    | want _ => rfl

/-- **A round that has ended takes no more fuel.** -/
theorem ends_exchange : ∀ (n : Nat) (X Y : List α) (c : Claim), Ends key ident h P n X Y c →
    ∀ j, exchange key ident h P (n + j) X Y c = exchange key ident h P n X Y c := by
  intro n
  induction n with
  | zero => intro _ _ _ he; exact he.elim
  | succ n ih =>
    intro X Y c he j
    rw [show n + 1 + j = (n + j) + 1 by omega]
    simp only [exchange]
    exact ends_fold_congr _ _ _ fun c' hc' => ih Y X c' (he c' hc') j

theorem Ends.succ : ∀ {n : Nat} {X Y : List α} {c : Claim}, Ends key ident h P n X Y c →
    Ends key ident h P (n + 1) X Y c
  | 0, _, _, _, he => he.elim
  | _ + 1, _, _, _, he => fun c' hc' => Ends.succ (he c' hc')

theorem Ends.le {n m : Nat} {X Y : List α} {c : Claim} (he : Ends key ident h P n X Y c) (hm : n ≤ m) :
    Ends key ident h P m X Y c := by
  induction hm with
  | refl => exact he
  | step _ ih => exact ih.succ

/-- A claim of ids is answered with ids only. -/
theorem ends_ids (X Y : List α) (r : Range) (xs : List ByteArray) :
    Ends key ident h P 1 X Y (.ids r xs) := by
  intro c' hc'
  simp [answer] at hc'

/-- A side holding at most `leaf` items in the range lists them. -/
theorem ends_few (X Y : List α) (r : Range) (n : Nat) (l : ByteArray)
    (hx : (within key r X).length ≤ P.leaf) : Ends key ident h P 2 X Y (.fp r n l) := by
  intro c' hc'
  by_cases hf : fp key ident h (within key r X) = (n, l)
  · simp [answer, hf] at hc'
  · simp only [answer, hf, hx, ↓reduceIte, List.mem_cons, Out.claim.injEq, List.not_mem_nil,
      or_false] at hc'
    subst hc'
    exact ends_ids Y X r _

/-! ## The size of a piece -/

theorem within_append (r : Range) (a b : List α) : within key r (a ++ b) = within key r a ++ within key r b :=
  List.filter_append ..

theorem within_none {r : Range} {l : List α} (h0 : ∀ a ∈ l, r.has (key a) = false) : within key r l = [] :=
  List.filter_eq_nil_iff.2 fun a ha => by simp [h0 a ha]

/-- Pieces cut at sorted items' keys: each holds at most s of them. The
first piece also holds `pre`, the items before x already in it. -/
theorem pick_pieces (s : Nat) (hs : 1 ≤ s) : ∀ (x : List α) (k : Nat) (pre : List α) (lo : Key)
    (hi : Option Key), Sorted key (pre ++ x) → (∀ a ∈ pre ++ x, ¬ key a < lo) → pre.length + k ≤ s →
    ∀ q ∈ pieces ⟨lo, hi⟩ ((pick s k x).map key), (within key q (pre ++ x)).length ≤ s
  | [], k, pre, lo, hi, _, _, hk => by
    intro q hq
    simp only [pick, List.map_nil, pieces, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    have := List.length_filter_le (fun a => Range.has ⟨lo, hi⟩ (key a)) (pre ++ [])
    simp only [List.append_nil] at this ⊢
    exact Nat.le_trans this (by omega)
  | a :: t, 0, pre, lo, hi, so, hlo, hk => by
    intro q hq
    simp only [pick, List.map_cons, pieces, List.mem_cons] at hq
    have sat : Sorted key (a :: t) := List.Pairwise.sublist (List.sublist_append_right _ _) so
    have hpre : ∀ b ∈ pre, key b < key a := fun b hb =>
      List.pairwise_append.1 so |>.2.2 b hb a (List.mem_cons_self ..)
    have hta : ∀ b ∈ t, key a < key b := (List.pairwise_cons.1 sat).1
    rcases hq with rfl | hq
    · -- [lo, key a): only `pre`
      rw [within_append, within_none (l := a :: t)]
      · have := List.length_filter_le (fun b => Range.has ⟨lo, some (key a)⟩ (key b)) pre
        simp only [List.append_nil]
        exact Nat.le_trans this (by omega)
      · intro b hb
        rw [← Bool.not_eq_true, has_iff]
        intro ⟨_, h2⟩
        have hlt := h2 _ rfl
        rcases List.mem_cons.1 hb with rfl | hb
        · exact Key.lt_irrefl _ hlt
        · exact Key.lt_irrefl _ (Key.lt_trans hlt (hta b hb))
    · -- the later pieces: from key a on, `pre` is behind them
      have hcs : ∀ k ∈ (pick s (s - 1) t).map key, key a < k := by
        intro k hk
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hk
        exact hta b (pick_sub _ _ _ b hb)
      have hql : key a = q.lo ∨ key a < q.lo := by
        rcases (pieces_ends _ _ q hq).1 with e | e
        · exact Or.inl e.symm
        · exact Or.inr (hcs _ e)
      rw [within_append, within_none (l := pre), List.nil_append]
      · have := pick_pieces s hs t (s - 1) [a] (key a) hi (by simpa using sat)
          (by
            intro b hb
            simp only [List.singleton_append, List.mem_cons] at hb
            rcases hb with rfl | hb
            · exact Key.lt_irrefl _
            · exact Key.lt_asymm (hta b hb))
          (by simp; omega) q hq
        simpa using this
      · intro b hb
        rw [← Bool.not_eq_true, has_iff]
        intro ⟨h1, _⟩
        apply h1
        rcases hql with e | e
        · rw [← e]; exact hpre b hb
        · exact Key.lt_trans (hpre b hb) e
  | a :: t, k + 1, pre, lo, hi, so, hlo, hk => by
    intro q hq
    simp only [pick] at hq
    have := pick_pieces s hs t k (pre ++ [a]) lo hi (by simpa using so) (by simpa using hlo)
      (by simp; omega) q hq
    simpa using this

/-- A piece of r lies in r, so the items there are the range's. -/
theorem within_sub {q r : Range} (hs : ∀ k, q.has k = true → r.has k = true) (X : List α) :
    within key q X = within key q (within key r X) := by
  unfold within
  rw [List.filter_filter]
  congr 1
  funext a
  by_cases hq : q.has (key a) = true
  · simp [hq, hs _ hq]
  · simp [hq]

/-- **A cut leaves each piece at most ⌈count/fan⌉ of the cutter's
items.** -/
theorem piece_size {X : List α} {r : Range} (sX : Sorted key X) (hlen : P.leaf < (within key r X).length) :
    ∀ q ∈ pieces r (cutsOf key P (within key r X)),
      (within key q X).length ≤ runLen P (within key r X).length := by
  intro q hq
  have hleaf := P.leaf_pos
  have sub := (pieces_shrink sX hlen q hq).2
  rw [within_sub sub X]
  have hs : 1 ≤ runLen P (within key r X).length := (runLen_bounds (P := P) (by omega)).1
  have sx : Sorted key (within key r X) := List.Pairwise.filter _ sX
  have := pick_pieces (key := key) _ hs (within key r X) (runLen P (within key r X).length) [] r.lo r.hi
    (by simpa using sx)
    (by
      intro a ha
      simp only [List.nil_append] at ha
      exact ((has_iff r (key a)).1 (mem_within.1 ha).2).1)
    (by simp) q (by unfold cutsOf at hq; exact hq)
  simpa using this

/-- A run of ⌈L/fan⌉ is at most leaf·fanᵏ when L is at most leaf·fanᵏ⁺¹. -/
theorem runLen_fan_le {L k : Nat} (hL : L ≤ P.leaf * P.fan ^ (k + 1)) : runLen P L ≤ P.leaf * P.fan ^ k := by
  have hf := P.fan_two
  unfold runLen
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  rw [Nat.pow_succ, ← Nat.mul_assoc] at hL
  rw [Nat.succ_mul]
  omega

/-! ## Messages per path -/

/-- **Each path of a round ends within 2k + 2 answers**, when each side
holds at most leaf·fanᵏ items in the claim's range. -/
theorem ends_log : ∀ (k : Nat) (X Y : List α) (c : Claim), Sorted key X → Sorted key Y →
    (within key c.range X).length ≤ P.leaf * P.fan ^ k →
    (within key c.range Y).length ≤ P.leaf * P.fan ^ k →
    Ends key ident h P (2 * k + 2) X Y c := by
  intro k
  induction k with
  | zero =>
    intro X Y c _ _ hX _
    cases c with
    | ids r xs => exact (ends_ids X Y r xs).le (by omega)
    | fp r n l => exact ends_few X Y r n l (by simpa [Claim.range] using hX)
  | succ k ih =>
    intro X Y c sX sY hX hY
    cases c with
    | ids r xs => exact (ends_ids X Y r xs).le (by omega)
    | fp r n l =>
      simp only [Claim.range] at hX hY
      by_cases hx : (within key r X).length ≤ P.leaf
      · exact (ends_few X Y r n l hx).le (by omega)
      · have hx' : P.leaf < (within key r X).length := by omega
        intro c' hc'
        by_cases hf : fp key ident h (within key r X) = (n, l)
        · simp [answer, hf] at hc'
        · simp only [answer, hf, hx, ↓reduceIte] at hc'
          obtain ⟨q, hq, e⟩ := List.mem_map.1 hc'
          cases e
          -- Y answers piece q of X's cut
          have hqX : (within key q X).length ≤ P.leaf * P.fan ^ k :=
            Nat.le_trans (piece_size sX hx' q (List.mem_reverse.1 hq)) (runLen_fan_le hX)
          have hqr := (pieces_shrink sX hx' q (List.mem_reverse.1 hq)).2
          have hqY : (within key q Y).length ≤ P.leaf * P.fan ^ (k + 1) :=
            Nat.le_trans (filter_len_le fun a ha => hqr _ ha) hY
          intro c'' hc''
          by_cases hne : fp key ident h (within key q Y) =
              ((fp key ident h (within key q X)).1, (fp key ident h (within key q X)).2)
          · simp [answer, hne] at hc''
          · by_cases hy : (within key q Y).length ≤ P.leaf
            · simp only [answer, hne, hy, ↓reduceIte, List.mem_cons, Out.claim.injEq,
                List.not_mem_nil, or_false] at hc''
              subst hc''
              exact (ends_ids X Y q _).le (by omega)
            · simp only [answer, hne, hy, ↓reduceIte] at hc''
              have hy' : P.leaf < (within key q Y).length := by omega
              obtain ⟨q', hq', e⟩ := List.mem_map.1 hc''
              cases e
              have hq'Y : (within key q' Y).length ≤ P.leaf * P.fan ^ k :=
                Nat.le_trans (piece_size sY hy' q' (List.mem_reverse.1 hq')) (runLen_fan_le hqY)
              have hq'r := (pieces_shrink sY hy' q' (List.mem_reverse.1 hq')).2
              have hq'X : (within key q' X).length ≤ P.leaf * P.fan ^ k :=
                Nat.le_trans (filter_len_le fun a ha => hq'r _ ha) hqX
              exact ih X Y _ sX sY hq'X hq'Y

theorem honest_range {Y : List α} {r : Range} {c : Claim} (hc : Honest key ident h Y r c) : c.range = r := by
  cases c with
  | fp r' _ _ => exact hc.1
  | ids r' _ => exact hc.1


end

/-! ## Cutting -/

/-- The picks of every s-th item from position k: at most (n + s − 1 − k)/s. -/
theorem pick_len {α : Type} (s : Nat) (hs : 1 ≤ s) : ∀ (k : Nat) (l : List α),
    (pick s k l).length * s ≤ l.length + (s - 1) - k
  | _, [] => by simp [pick]
  | 0, a :: t => by
    have ih := pick_len s hs (s - 1) t
    simp only [pick, List.length_cons, Nat.succ_mul]
    omega
  | k + 1, _ :: t => by
    have ih := pick_len s hs k t
    simp only [pick, List.length_cons]
    omega

theorem pieces_len (r : Range) : ∀ cs : List Key, (pieces r cs).length = cs.length + 1
  | [] => rfl
  | _ :: cs => by simp [pieces, pieces_len _ cs]

/-- A run length of ⌈L/f⌉ covers L items in f runs. -/
theorem div_ceil_mul (L f : Nat) (hf : 0 < f) : L ≤ (L + f - 1) / f * f := by
  have h1 := Nat.div_add_mod (L + f - 1) f
  have h2 := Nat.mod_lt (L + f - 1) hf
  have h3 : L + f - 1 + 1 = L + f := by omega
  generalize (L + f - 1) / f = q at h1 ⊢
  generalize (L + f - 1) % f = r at h1 h2
  generalize L + f - 1 = A at h1 h3
  rw [Nat.mul_comm]
  omega

/-- **A range is cut into at most `fan` pieces.** -/
theorem pieces_count {α : Type} (key : α → Key) (P : Params) (r : Range) (x : List α) :
    (pieces r (cutsOf key P x)).length ≤ P.fan := by
  have hf := P.fan_two
  rw [pieces_len]
  unfold cutsOf
  rw [List.length_map]
  cases x with
  | nil => simp [pick] <;> omega
  | cons a t =>
    have hl := div_ceil_mul (a :: t).length P.fan (by omega)
    have hs1 : 1 ≤ runLen P (a :: t).length := by
      rcases Nat.eq_zero_or_pos (runLen P (a :: t).length) with h0 | h0
      · unfold runLen at h0
        rw [h0] at hl
        simp at hl
      · exact h0
    have hl' : (a :: t).length ≤ runLen P (a :: t).length * P.fan := hl
    have hL : 1 ≤ (a :: t).length := by simp
    clear hl
    generalize runLen P (a :: t).length = s at hs1 hl' ⊢
    have hp := pick_len s hs1 s (a :: t)
    generalize (pick s s (a :: t)).length = k at hp ⊢
    generalize (a :: t).length = L at hp hl' hL
    have : k * s < P.fan * s := by
      rw [Nat.mul_comm P.fan]; omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega

end Engine.Sync
