/-
What one round does, proven of `exchange`, which is the two sides'
`answer`s composed:

- `exchange_complete`: from an honest claim over r, each side is sent
  exactly the ids the other holds in r and it lacks.
- It needs: each side's items sorted by key (as its index keeps them),
  items named by their keys and ids across both sides (`Named`, from
  `Distinct` and `num_inj`), and no hash collision in what the two sides'
  labels of any range hashed (`Sound`, the collision assumption).
- Fuel: a round from r ends within |X ∩ r| + |Y ∩ r| + 1 answers on any
  path (each piece holds fewer of the cutting side's items).
-/
import ops.sync.Round

namespace Engine.Sync

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray)

/-- Items sorted by key, as an index keeps them. -/
def Sorted (l : List α) : Prop := l.Pairwise fun a b => key a < key b

/-- No collision in what either side's label of any range hashes. -/
def Sound (X Y : List α) : Prop :=
  ∀ r, NoCollision h (pres key ident h (within key r X) ++ pres key ident h (within key r Y))

/-- A claim Y can honestly make about r. -/
def Honest (Y : List α) (r : Range) : Claim → Prop
  | .fp r' n l => r' = r ∧ (n, l) = fp key ident h (within key r Y)
  | .ids r' xs => r' = r ∧ xs = (within key r Y).map ident

end

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

theorem named_iff {l : List α} {i : ByteArray} : named ident l i = true ↔ ∃ a ∈ l, ident a = i := by
  simp [named, List.any_eq_true]

theorem named_false {l : List α} {i : ByteArray} : named ident l i = false ↔ ∀ a ∈ l, ident a ≠ i := by
  rw [← Bool.not_eq_true, named_iff]; simp

theorem mem_within {r : Range} {l : List α} {a : α} : a ∈ within key r l ↔ a ∈ l ∧ r.has (key a) = true := by
  simp [within, List.mem_filter]

theorem Sound.symm {X Y : List α} (s : Sound key ident h X Y) : Sound key ident h Y X :=
  fun r => nocol_sub (s r) (fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_right _ ha
    · exact List.mem_append_left _ ha)

theorem named_symm {X Y : List α} (n : Named key ident (X ++ Y)) : Named key ident (Y ++ X) :=
  named_sub n (fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_right _ ha
    · exact List.mem_append_left _ ha)

theorem mem_fold (sub : Claim → List ByteArray × List ByteArray) (os : List Out) (i : ByteArray) :
    (i ∈ (os.foldr (fun o acc => (give sub o ++ acc.1, get sub o ++ acc.2)) ([], [])).1 ↔
      ∃ o ∈ os, i ∈ give sub o) ∧
    (i ∈ (os.foldr (fun o acc => (give sub o ++ acc.1, get sub o ++ acc.2)) ([], [])).2 ↔
      ∃ o ∈ os, i ∈ get sub o) := by
  induction os with
  | nil => simp
  | cons o t ih =>
    simp only [List.foldr_cons, List.mem_append, ih.1, ih.2, List.mem_cons, or_and_right, exists_or,
      exists_eq_left, and_self]

theorem filter_len_le {l : List α} {p q : α → Bool} (hq : ∀ a, q a = true → p a = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.filter_cons]
    by_cases hb : q b = true
    · simp [hb, hq b hb]; omega
    · by_cases hp : p b = true
      · simp [hb, hp]; omega
      · simp [hb, hp]; omega

theorem filter_len_lt {l : List α} {p q : α → Bool} (hq : ∀ a, q a = true → p a = true)
    (hx : ∃ a ∈ l, p a = true ∧ q a = false) : (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons b t ih =>
    simp only [List.filter_cons]
    obtain ⟨a, ha, hpa, hqa⟩ := hx
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [hpa, hqa]
      exact Nat.lt_succ_of_le (filter_len_le hq)
    · have := ih ⟨a, ha, hpa, hqa⟩
      by_cases hb : q b = true
      · simp [hb, hq b hb]; omega
      · by_cases hp : p b = true
        · simp [hb, hp]; omega
        · simp [hb, hp]; omega

/-- Answering a claim of ids: what this side holds there that the
claimant lacks, and what it lacks. -/
theorem exchange_ids (n : Nat) (X Y : List α) (r : Range) (xs : List ByteArray)
    (hc : xs = (within key r Y).map ident) (i : ByteArray) :
    (i ∈ (exchange key ident h P (n + 1) X Y (.ids r xs)).1 ↔
      named ident (within key r X) i = true ∧ named ident (within key r Y) i = false) ∧
    (i ∈ (exchange key ident h P (n + 1) X Y (.ids r xs)).2 ↔
      named ident (within key r Y) i = true ∧ named ident (within key r X) i = false) := by
  subst hc
  rw [exchange, (mem_fold _ _ i).1, (mem_fold _ _ i).2]
  simp only [answer, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, give, get,
    exists_eq_left, List.not_mem_nil, false_or, or_false]
  constructor
  · simp only [List.mem_map, List.mem_filter, Bool.not_eq_true', List.any_eq_false, List.mem_map,
      named_iff, named_false]
    constructor
    · rintro ⟨a, ⟨ha, hna⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, fun b hb e => ?_⟩
      exact absurd (by simp [e]) (hna (ident b) ⟨b, hb, rfl⟩)
    · rintro ⟨⟨a, ha, rfl⟩, hn⟩
      refine ⟨a, ⟨ha, fun j ⟨b, hb, e⟩ => ?_⟩, rfl⟩
      simp only [decide_eq_true_eq]
      intro e'
      exact hn b hb (e.trans e'.symm)
  · simp only [List.mem_filter, List.mem_map, Bool.not_eq_true', named_iff, named_false]

/-- Items named alike on both sides of a range: by `lbl_inj`. -/
theorem same_of_fp {X Y : List α} {r : Range} (nm : Named key ident (X ++ Y))
    (so : Sound key ident h X Y) (he : fp key ident h (within key r X) = fp key ident h (within key r Y)) :
    ∀ i, named ident (within key r X) i = named ident (within key r Y) i := by
  have hl : lbl key ident h (within key r X) = lbl key ident h (within key r Y) := (Prod.mk.inj he).2
  have hm := lbl_inj _ _ _ (Nat.le_refl _)
    (named_sub nm (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_append_left _ (mem_within.mp ha).1
      · exact List.mem_append_right _ (mem_within.mp ha).1))
    (so r) hl
  intro i
  apply Bool.eq_iff_iff.mpr
  simp only [named_iff]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, (hm a).mp ha, e⟩, fun ⟨a, ha, e⟩ => ⟨a, (hm a).mpr ha, e⟩⟩

/-- The run length is at least one and cuts at least twice. -/
theorem runLen_bounds {n : Nat} (hn : 2 ≤ n) : 1 ≤ runLen P n ∧ runLen P n < n := by
  have hf := P.fan_two
  unfold runLen
  constructor
  · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  · apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    have h1 : 2 * P.fan ≤ n * P.fan := Nat.mul_le_mul_right _ hn
    have h2 : n * 2 ≤ n * P.fan := Nat.mul_le_mul_left _ hf
    omega

/-- Cutting at the picked items: the first piece misses the first cut
item; every later piece misses the range's first item. So every piece
holds fewer of the cutter's items than the range does. -/
theorem pieces_shrink {X : List α} {r : Range} (sX : Sorted key X)
    (hlen : P.leaf < (within key r X).length) :
    ∀ q ∈ pieces r (cutsOf key P (within key r X)),
      (within key q X).length < (within key r X).length ∧
      (∀ k, q.has k = true → r.has k = true) := by
  have hleaf := P.leaf_pos
  have sx : Sorted key (within key r X) := List.Pairwise.filter _ sX
  have hcut : ∀ c ∈ cutsOf key P (within key r X), r.has c = true := by
    intro c hc
    simp only [cutsOf, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact (mem_within.mp (pick_sub _ _ _ p hp)).2
  intro q hq
  have hsub := pieces_sub _ r hcut q hq
  refine ⟨?_, hsub⟩
  generalize hx : within key r X = x at sx hlen hcut hq
  match x, sx, hlen, hcut, hq with
  | [], _, hlen, _, _ => simp at hlen
  | e0 :: rest, sx, hlen, hcut, hq =>
    have hb := runLen_bounds (P := P) (n := (e0 :: rest).length) (by omega)
    generalize hs : runLen P (e0 :: rest).length = s at hb
    obtain ⟨s1, s2⟩ := hb
    have hpick : ∀ p ∈ pick s s (e0 :: rest), p ∈ rest := by
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      intro p hp
      simp only [pick] at hp
      exact pick_sub _ _ _ p hp
    have hne := pick_ne s s (e0 :: rest) s2
    have hcuts : cutsOf key P (e0 :: rest) = (pick s s (e0 :: rest)).map key := by
      unfold cutsOf; rw [hs]
    rw [hcuts] at hq
    generalize hpl : pick s s (e0 :: rest) = pl at hpick hne hq
    match pl, hpick, hne, hq with
    | [], _, hne, _ => exact absurd rfl hne
    | p1 :: ps, hpick, _, hq =>
      have hp1 : p1 ∈ rest := hpick p1 (List.mem_cons_self ..)
      have hlt : ∀ p ∈ p1 :: ps, key e0 < key p := fun p hp =>
        (List.pairwise_cons.mp sx).1 p (hpick p hp)
      rw [← hx]
      apply filter_len_lt (fun a ha => by
        exact hsub _ ha)
      simp only [List.map_cons, pieces, List.mem_cons] at hq
      rcases hq with rfl | hq
      · have hx1 : p1 ∈ within key r X := by rw [hx]; exact List.mem_cons_of_mem _ hp1
        refine ⟨p1, (mem_within.mp hx1).1, (mem_within.mp hx1).2, ?_⟩
        rw [← Bool.not_eq_true, has_iff]
        exact fun h' => Key.lt_irrefl _ (h'.2 _ rfl)
      · have hx0 : e0 ∈ within key r X := by rw [hx]; exact List.mem_cons_self ..
        refine ⟨e0, (mem_within.mp hx0).1, (mem_within.mp hx0).2, ?_⟩
        obtain ⟨hlo, _⟩ := pieces_ends _ _ q hq
        have : key e0 < q.lo := by
          rcases hlo with hlo | hlo
          · rw [hlo]; exact hlt p1 (List.mem_cons_self ..)
          · simp only [List.mem_map] at hlo
            obtain ⟨p, hp, e⟩ := hlo
            rw [← e]; exact hlt p (List.mem_cons_of_mem _ hp)
        have hf : q.has (key e0) = false := by
          rw [← Bool.not_eq_true, has_iff]; exact fun h' => h'.1 this
        exact hf

/-- The pieces' differences make up the range's. -/
theorem pieces_diff {X Y : List α} {r : Range} {cs : List Key} (nm : Named key ident (X ++ Y))
    (hcut : ∀ c ∈ cs, r.has c = true) (i : ByteArray) :
    (∃ q ∈ pieces r cs, named ident (within key q X) i = true ∧ named ident (within key q Y) i = false) ↔
      named ident (within key r X) i = true ∧ named ident (within key r Y) i = false := by
  simp only [named_iff, named_false, mem_within]
  constructor
  · rintro ⟨q, hq, ⟨a, ⟨ha, hqa⟩, rfl⟩, hn⟩
    refine ⟨⟨a, ⟨ha, pieces_sub cs r hcut q hq _ hqa⟩, rfl⟩, fun b ⟨hb, _⟩ e => ?_⟩
    have := (nm a (List.mem_append_left _ ha) b (List.mem_append_right _ hb)).2 e.symm
    subst this
    exact hn a ⟨hb, hqa⟩ rfl
  · rintro ⟨⟨a, ⟨ha, hra⟩, rfl⟩, hn⟩
    obtain ⟨q, hq, hqa⟩ := pieces_cover cs r (key a) hra
    exact ⟨q, hq, ⟨a, ⟨ha, hqa⟩, rfl⟩, fun b ⟨hb, hqb⟩ e =>
      hn b ⟨hb, pieces_sub cs r hcut q hq _ hqb⟩ e⟩

/-- **A round is complete**: from Y's honest claim over r, X is sent
exactly what Y holds in r and X lacks, and Y exactly what X holds in r
and Y lacks, within |X ∩ r| + |Y ∩ r| + 1 answers on any path. -/
theorem exchange_complete : ∀ (n : Nat) (X Y : List α) (r : Range) (c : Claim),
    Sorted key X → Sorted key Y → Named key ident (X ++ Y) → Sound key ident h X Y →
    Honest key ident h Y r c → (within key r X).length + (within key r Y).length < n → ∀ i,
    (i ∈ (exchange key ident h P n X Y c).1 ↔
      named ident (within key r X) i = true ∧ named ident (within key r Y) i = false) ∧
    (i ∈ (exchange key ident h P n X Y c).2 ↔
      named ident (within key r Y) i = true ∧ named ident (within key r X) i = false) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ hn; omega
  | succ n ih =>
    intro X Y r c sX sY nm so hc hn i
    cases c with
    | ids r' xs =>
      obtain ⟨rfl, hxs⟩ := hc
      exact exchange_ids n X Y r' xs hxs i
    | fp r' cn cl =>
      obtain ⟨rfl, hfp⟩ := hc
      by_cases hf : fp key ident h (within key r' X) = (cn, cl)
      · -- Settled: the two sides hold the same items in r.
        have hsame := same_of_fp nm so (hf.trans hfp)
        have he : exchange key ident h P (n + 1) X Y (.fp r' cn cl) = ([], []) := by
          rw [exchange]; simp [answer, hf]
        rw [he, hsame i]
        simp only [List.not_mem_nil, false_iff]
        constructor <;> intro ⟨h1, h2⟩ <;> rw [h1] at h2 <;> cases h2
      · by_cases hl : (within key r' X).length ≤ P.leaf
        · -- Few items here: answer with them all.
          rw [exchange, (mem_fold _ _ i).1, (mem_fold _ _ i).2]
          have ha : answer key ident h P X (.fp r' cn cl) =
              [.claim (.ids r' ((within key r' X).map ident))] := by
            simp [answer, hf, hl]
          rw [ha]
          simp only [List.mem_cons, List.mem_nil_iff, or_false, exists_eq_left, give, get]
          have hn1 : ∃ k, n = k + 1 := by
            have : 0 < (within key r' X).length + (within key r' Y).length := by
              rcases Nat.eq_zero_or_pos ((within key r' X).length + (within key r' Y).length) with
                h0 | h0
              · have e1 : within key r' X = [] := List.eq_nil_of_length_eq_zero (by omega)
                have e2 : within key r' Y = [] := List.eq_nil_of_length_eq_zero (by omega)
                exact absurd (by rw [e1]; rw [e2] at hfp; exact hfp.symm) hf
              · exact h0
            exact ⟨n - 1, by omega⟩
          obtain ⟨k, rfl⟩ := hn1
          have := exchange_ids (key := key) (ident := ident) (h := h) (P := P) k Y X r'
            ((within key r' X).map ident) rfl i
          exact ⟨this.2, this.1⟩
        · -- Many items here: cut the range; each piece is a round of its own.
          have hl' : P.leaf < (within key r' X).length := by omega
          rw [exchange, (mem_fold _ _ i).1, (mem_fold _ _ i).2]
          have ha : answer key ident h P X (.fp r' cn cl) =
              (pieces r' (cutsOf key P (within key r' X))).map fun q =>
                .claim (.fp q (fp key ident h (within key q X)).1 (fp key ident h (within key q X)).2) := by
            simp [answer, hf, hl]
          rw [ha]
          have hcut : ∀ c ∈ cutsOf key P (within key r' X), r'.has c = true := by
            intro c hc
            simp only [cutsOf, List.mem_map] at hc
            obtain ⟨p, hp, rfl⟩ := hc
            exact (mem_within.mp (pick_sub _ _ _ p hp)).2
          have hsub : ∀ q ∈ pieces r' (cutsOf key P (within key r' X)),
              (within key q Y).length ≤ (within key r' Y).length := fun q hq =>
            filter_len_le (fun a ha => (pieces_shrink sX hl' q hq).2 _ ha)
          have sub := fun q hq => ih Y X q
            (.fp q (fp key ident h (within key q X)).1 (fp key ident h (within key q X)).2)
            sY sX (named_symm nm) so.symm ⟨rfl, rfl⟩
            (by have := (pieces_shrink (P := P) sX hl' q hq).1; have := hsub q hq; omega) i
          have hmap : ∀ (f : Out → List ByteArray), (∃ o ∈ (pieces r' (cutsOf key P (within key r' X))).map
              (fun q => Out.claim (.fp q (fp key ident h (within key q X)).1 (fp key ident h (within key q X)).2)),
              i ∈ f o) ↔ ∃ q ∈ pieces r' (cutsOf key P (within key r' X)),
              i ∈ f (.claim (.fp q (fp key ident h (within key q X)).1 (fp key ident h (within key q X)).2)) := by
            intro f
            constructor
            · rintro ⟨o, ho, hi⟩
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
              exact ⟨q, hq, hi⟩
            · rintro ⟨q, hq, hi⟩
              exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, hi⟩
          rw [hmap, hmap]
          simp only [give, get]
          constructor
          · rw [← pieces_diff nm hcut i]
            exact ⟨fun ⟨q, hq, hi⟩ => ⟨q, hq, (sub q hq).2.mp hi⟩,
              fun ⟨q, hq, hi⟩ => ⟨q, hq, (sub q hq).2.mpr hi⟩⟩
          · rw [← pieces_diff (named_symm nm) hcut i]
            exact ⟨fun ⟨q, hq, hi⟩ => ⟨q, hq, (sub q hq).1.mp hi⟩,
              fun ⟨q, hq, hi⟩ => ⟨q, hq, (sub q hq).1.mpr hi⟩⟩

/-- How a side opens a round is an honest claim. -/
theorem opening_honest (Y : List α) (r : Range) :
    Honest key ident h Y r (opening key ident h P Y r) := by
  unfold opening
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

end

end Engine.Sync
