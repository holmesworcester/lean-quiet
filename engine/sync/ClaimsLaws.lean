/-
How many claims a round answers, proven of `exchange`'s structure (the
two sides' `answer`s composed).

- `tally n X Y c`: the claims answered in a round from claim c (which X
  answers), within n answers on any path: c and every claim below it.
- `delta X Y`: the items on one side only.
- **A range with no difference settles** (`fp_of_same`): two sorted
  lists with the same items are one list (`sorted_eq`), so their
  fingerprints match, and no hash assumption is needed for it.
- **The pieces split the difference** (`pieces_delta`): the pieces of a
  cut are disjoint parts of the range, so their differences add up to
  at most the range's.
- **Claims** (`tally_le`): an honest claim over r costs at most
  1 + fan·n·|Δ ∩ r| claims within n answers, Δ the difference; with the
  2k + 2 answers a round needs (`ends_log`), at most
  1 + fan·(2k + 2)·|Δ ∩ r| (`claims_log`), whatever fuel it is given.
-/
import engine.sync.DepthLaws

namespace Engine.Sync

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- The claims a round from c answers, within n answers on any path. -/
def tally : Nat → List α → List α → Claim → Nat
  | 0, _, _, _ => 0
  | n + 1, X, Y, c => 1 + ((answer key ident h P X c).map fun o => match o with
      | .claim c' => tally n Y X c'
      | _ => 0).sum

/-- The items on one side only. -/
def delta (X Y : List α) : List α :=
  X.filter (fun a => !named ident Y (ident a)) ++ Y.filter (fun b => !named ident X (ident b))

end

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

/-! ## A range with no difference settles -/

/-- **Two sorted lists with the same items are one list.** -/
theorem sorted_eq : ∀ {l₁ l₂ : List α}, Sorted key l₁ → Sorted key l₂ → (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, he => absurd ((he b).2 (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, he => absurd ((he a).1 (List.mem_cons_self ..)) (by simp)
  | a :: t, b :: u, s1, s2, he => by
    have ha := (List.pairwise_cons.1 s1).1
    have hb := (List.pairwise_cons.1 s2).1
    have eab : a = b := by
      rcases List.mem_cons.1 ((he a).1 (List.mem_cons_self ..)) with e | hau
      · exact e
      · rcases List.mem_cons.1 ((he b).2 (List.mem_cons_self ..)) with e | hbt
        · exact e.symm
        · exact absurd (ha b hbt) (Key.lt_asymm (hb a hau))
    subst eab
    have ht : ∀ x, x ∈ t ↔ x ∈ u := by
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.1 ((he x).1 (List.mem_cons_of_mem _ hx)) with e | hu
        · subst e; exact absurd (ha x hx) (Key.lt_irrefl _)
        · exact hu
      · intro hx
        rcases List.mem_cons.1 ((he x).2 (List.mem_cons_of_mem _ hx)) with e | hu
        · subst e; exact absurd (hb x hx) (Key.lt_irrefl _)
        · exact hu
    rw [sorted_eq (List.pairwise_cons.1 s1).2 (List.pairwise_cons.1 s2).2 ht]

/-- **A range whose difference is empty has one fingerprint on both
sides.** -/
theorem fp_of_same {X Y : List α} {r : Range} (sX : Sorted key X) (sY : Sorted key Y)
    (nm : Named key ident (X ++ Y)) (hd : within key r (delta ident X Y) = []) :
    fp key ident h (within key r X) = fp key ident h (within key r Y) := by
  have side : ∀ {A B : List α}, Named key ident (A ++ B) →
      (∀ a ∈ A, r.has (key a) = true → named ident B (ident a) = true) →
      ∀ a, a ∈ within key r A → a ∈ within key r B := by
    intro A B nmAB hAB a ha
    obtain ⟨haA, har⟩ := mem_within.1 ha
    obtain ⟨b, hbB, e⟩ := named_iff.1 (hAB a haA har)
    have := (nmAB b (List.mem_append_right _ hbB) a (List.mem_append_left _ haA)).2 e
    subst this
    exact mem_within.2 ⟨hbB, har⟩
  have hx : ∀ a ∈ X, r.has (key a) = true → named ident Y (ident a) = true := by
    intro a ha hr
    cases hn : named ident Y (ident a) with
    | true => rfl
    | false =>
      have : a ∈ within key r (delta ident X Y) :=
        mem_within.2 ⟨List.mem_append_left _ (List.mem_filter.2 ⟨ha, by simp [hn]⟩), hr⟩
      rw [hd] at this; cases this
  have hy : ∀ b ∈ Y, r.has (key b) = true → named ident X (ident b) = true := by
    intro b hb hr
    cases hn : named ident X (ident b) with
    | true => rfl
    | false =>
      have : b ∈ within key r (delta ident X Y) :=
        mem_within.2 ⟨List.mem_append_right _ (List.mem_filter.2 ⟨hb, by simp [hn]⟩), hr⟩
      rw [hd] at this; cases this
  have e : within key r X = within key r Y :=
    sorted_eq (List.Pairwise.filter _ sX) (List.Pairwise.filter _ sY)
      (fun a => ⟨side nm hx a, side (named_symm nm) hy a⟩)
  rw [e]

theorem delta_len (X Y : List α) (r : Range) :
    (within key r (delta ident Y X)).length = (within key r (delta ident X Y)).length := by
  simp only [delta, within_append, List.length_append]
  omega

/-! ## The pieces split the difference -/

theorem filter_add_le {l : List α} {p q s : α → Bool} (hpq : ∀ a, ¬ (p a = true ∧ q a = true))
    (hp : ∀ a, p a = true → s a = true) (hq : ∀ a, q a = true → s a = true) :
    (l.filter p).length + (l.filter q).length ≤ (l.filter s).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    have := hpq a
    by_cases h1 : p a = true
    · simp [h1, hp a h1, show q a = false by simpa [h1] using this]; omega
    · by_cases h2 : q a = true
      · simp [h1, h2, hq a h2]; omega
      · by_cases h3 : s a = true
        · simp [h1, h2, h3]; omega
        · simp [h1, h2, h3]; omega

/-- **Cut at increasing keys inside it, a range's pieces hold its
difference between them.** -/
theorem pieces_delta (D : List α) : ∀ (cs : List Key) (r : Range), cs.Pairwise (· < ·) →
    (∀ c ∈ cs, r.has c = true) →
    ((pieces r cs).map fun q => (within key q D).length).sum ≤ (within key r D).length
  | [], r, _, _ => by simp [pieces]
  | c :: cs, r, hs, hin => by
    have hc := (has_iff r c).1 (hin c (List.mem_cons_self ..))
    have ih := pieces_delta D cs ⟨c, r.hi⟩ (List.pairwise_cons.1 hs).2 (by
      intro c' hc'
      have h1 := (List.pairwise_cons.1 hs).1 c' hc'
      have h2 := (has_iff r c').1 (hin c' (List.mem_cons_of_mem _ hc'))
      rw [has_iff]
      exact ⟨Key.lt_asymm h1, h2.2⟩)
    simp only [pieces, List.map_cons, List.sum_cons]
    have hsplit : (within key ⟨r.lo, some c⟩ D).length + (within key ⟨c, r.hi⟩ D).length ≤
        (within key r D).length := by
      unfold within
      apply filter_add_le
      · intro a ⟨h1, h2⟩
        rw [has_iff] at h1 h2
        exact h2.1 (h1.2 c rfl)
      · intro a h1
        rw [has_iff] at h1 ⊢
        refine ⟨h1.1, fun hh e => ?_⟩
        exact Key.lt_trans (h1.2 c rfl) (hc.2 hh e)
      · intro a h2
        rw [has_iff] at h2 ⊢
        refine ⟨fun hlt => ?_, h2.2⟩
        rcases Key.not_lt.1 h2.1 with h' | h'
        · exact hc.1 (Key.lt_trans h' hlt)
        · have e : key a = c := h'
          exact hc.1 (e ▸ hlt)
    omega

theorem pick_sublist (s : Nat) : ∀ (k : Nat) (l : List α), (pick s k l).Sublist l
  | _, [] => by simp [pick]
  | 0, a :: t => by simp only [pick]; exact (pick_sublist s _ t).cons_cons a
  | k + 1, _ :: t => by simp only [pick]; exact (pick_sublist s k t).cons _

theorem cuts_sorted {x : List α} (sx : Sorted key x) : (cutsOf key P x).Pairwise (· < ·) := by
  unfold cutsOf
  exact List.pairwise_map.2 (List.Pairwise.sublist (pick_sublist _ _ _) sx)

/-! ## Claims -/

theorem sum_map_le {β : Type} (l : List β) {f g : β → Nat} (hfg : ∀ b ∈ l, f b ≤ g b) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hfg b (List.mem_cons_self ..)
    have := ih fun c hc => hfg c (List.mem_cons_of_mem _ hc)
    omega

theorem sum_map_affine {β : Type} (l : List β) (K : Nat) (d : β → Nat) :
    (l.map fun b => 1 + K * d b).sum = l.length + K * (l.map d).sum := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add]
    omega

theorem tally_ids : ∀ (n : Nat) (X Y : List α) (r : Range) (xs : List ByteArray),
    tally key ident h P n X Y (.ids r xs) ≤ 1
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, X, Y, r, xs => by simp [tally, answer]

/-- **An honest claim over r is answered with at most 1 + fan·n·|Δ ∩ r|
claims within n answers**, Δ the items on one side only. -/
theorem tally_le : ∀ (n : Nat) (X Y : List α) (r : Range) (c : Claim),
    Sorted key X → Sorted key Y → Named key ident (X ++ Y) → Honest key ident h Y r c →
    tally key ident h P n X Y c ≤ 1 + P.fan * n * (within key r (delta ident X Y)).length := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _; simp [tally]
  | succ n ih =>
    intro X Y r c sX sY nm hc
    have hfan := P.fan_two
    cases c with
    | ids r' xs => have := tally_ids (key := key) (ident := ident) (h := h) (P := P) (n + 1) X Y r' xs; omega
    | fp r' cn cl =>
      obtain ⟨rfl, hfp⟩ := hc
      by_cases hf : fp key ident h (within key r' X) = (cn, cl)
      · simp [tally, answer, hf]
      · -- a mismatch: the range holds a difference
        have hD : 1 ≤ (within key r' (delta ident X Y)).length := by
          rcases Nat.eq_zero_or_pos (within key r' (delta ident X Y)).length with h0 | h0
          · exact absurd ((fp_of_same sX sY nm (List.eq_nil_of_length_eq_zero h0)).trans hfp.symm) hf
          · exact h0
        generalize hd : (within key r' (delta ident X Y)).length = d at hD
        have hK : P.fan ≤ P.fan * (n + 1) * d := by
          have : 1 ≤ (n + 1) * d := Nat.mul_pos (by omega) hD
          calc P.fan = P.fan * 1 := (Nat.mul_one _).symm
            _ ≤ P.fan * ((n + 1) * d) := Nat.mul_le_mul_left _ this
            _ = P.fan * (n + 1) * d := (Nat.mul_assoc _ _ _).symm
        by_cases hl : (within key r' X).length ≤ P.leaf
        · simp only [tally, answer, hf, hl, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]
          have := tally_ids (key := key) (ident := ident) (h := h) (P := P) n Y X r'
            ((within key r' X).map ident)
          omega
        · have hl' : P.leaf < (within key r' X).length := by omega
          simp only [tally, answer, hf, hl, ↓reduceIte, List.map_map]
          have hcut : ∀ c' ∈ cutsOf key P (within key r' X), r'.has c' = true := by
            intro c' hc'
            simp only [cutsOf, List.mem_map] at hc'
            obtain ⟨p, hp, rfl⟩ := hc'
            exact (mem_within.1 (pick_sub _ _ _ p hp)).2
          have hsub : ∀ q ∈ pieces r' (cutsOf key P (within key r' X)),
              tally key ident h P n Y X (.fp q (fp key ident h (within key q X)).1 (fp key ident h (within key q X)).2) ≤
                1 + P.fan * n * (within key q (delta ident X Y)).length := by
            intro q _
            have := ih Y X q (.fp q (fp key ident h (within key q X)).1 (fp key ident h (within key q X)).2)
              sY sX (named_symm nm) ⟨rfl, rfl⟩
            rwa [delta_len] at this
          have h1 := sum_map_le _ hsub
          rw [sum_map_affine] at h1
          have h2 := pieces_delta (key := key) (delta ident X Y) _ r'
            (cuts_sorted (P := P) (List.Pairwise.filter _ sX)) hcut
          rw [hd] at h2
          have h3 := pieces_count key P r' (within key r' X)
          have h4 : P.fan * n * ((pieces r' (cutsOf key P (within key r' X))).map
              fun q => (within key q (delta ident X Y)).length).sum ≤ P.fan * n * d :=
            Nat.mul_le_mul_left _ h2
          have e : P.fan * (n + 1) * d = P.fan * n * d + P.fan * d := by
            rw [Nat.mul_succ, Nat.add_mul]
          have h5 : P.fan ≤ P.fan * d := Nat.le_mul_of_pos_right _ hD
          have hfun : (fun o : Out => match o with
              | .claim c' => tally key ident h P n Y X c'
              | _ => 0) ∘ (fun q => Out.claim (.fp q (fp key ident h (within key q X)).1
                (fp key ident h (within key q X)).2)) =
              fun q => tally key ident h P n Y X (.fp q (fp key ident h (within key q X)).1
                (fp key ident h (within key q X)).2) := rfl
          rw [hfun]
          omega

/-- A round that has ended answers no more claims with more fuel. -/
theorem tally_stable : ∀ (n : Nat) (X Y : List α) (c : Claim), Ends key ident h P n X Y c →
    ∀ j, tally key ident h P (n + j) X Y c = tally key ident h P n X Y c := by
  intro n
  induction n with
  | zero => intro _ _ _ he; exact he.elim
  | succ n ih =>
    intro X Y c he j
    rw [show n + 1 + j = (n + j) + 1 by omega]
    simp only [tally]
    congr 2
    apply List.map_congr_left
    intro o ho
    cases o with
    | claim c' => exact ih Y X c' (he c' ho) j
    | hold _ => rfl
    | want _ => rfl

/-- **A round answers at most 1 + fan·(2k + 2)·|Δ ∩ r| claims** when each
side holds at most leaf·fanᵏ items in r, whatever fuel it is given. -/
theorem claims_log (k : Nat) (X Y : List α) (r : Range) (c : Claim) (sX : Sorted key X) (sY : Sorted key Y)
    (nm : Named key ident (X ++ Y)) (hc : Honest key ident h Y r c)
    (hX : (within key r X).length ≤ P.leaf * P.fan ^ k) (hY : (within key r Y).length ≤ P.leaf * P.fan ^ k)
    (j : Nat) :
    tally key ident h P (2 * k + 2 + j) X Y c ≤ 1 + P.fan * (2 * k + 2) * (within key r (delta ident X Y)).length := by
  have hr := honest_range hc
  have he := ends_log (ident := ident) (h := h) (P := P) k X Y c sX sY (hr ▸ hX) (hr ▸ hY)
  rw [tally_stable _ X Y c he j]
  exact tally_le _ X Y r c sX sY nm hc

end

end Engine.Sync
