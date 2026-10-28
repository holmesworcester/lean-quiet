/-
The index of windows finds exactly the windows that hold a position,
and netting keeps exactly what a batch changed (engine/core/Window.lean).

- `rank_spec`: the binary search counts the bounds before p.
- `find_build`: a key's slots, built from its windows, find exactly the
  windows whose range holds p. Every window's ends are bounds, so a
  position between two bounds is held by the windows that hold the gap,
  which `covers` decides from the bounds alone.
- `find_iff`: the subscriptions find exactly the subscribers with a
  window holding a row filed under k at p; `add`, `keep` and `ofList`
  keep the index well formed and change exactly the subscriptions they
  name.
- `mem_net`: the net filings are the (key, position) pairs the journal
  touched an odd number of times.
-/
import engine.core.Window
import engine.core.Order

namespace Engine

theorem lawfulBEqByteArray : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

attribute [local instance] lawfulBEqByteArray

/-! ## Positions as a strict order -/

theorem Pos.lt_swap {p q : Pos} (h : p.cmp q = .lt) : q.cmp p = .gt := by
  rw [Pos.cmp_swap, h]; rfl

theorem Pos.gt_swap {p q : Pos} (h : p.cmp q = .gt) : q.cmp p = .lt := by
  rw [Pos.cmp_swap, h]; rfl

theorem Pos.cmp_self (p : Pos) : p.cmp p = .eq := (Pos.cmp_eq_iff p p).2 rfl

theorem Pos.lt_of_lt_le {p q r : Pos} (h1 : p.cmp q = .lt) (h2 : q.cmp r ≠ .gt) : p.cmp r = .lt := by
  rcases e : q.cmp r with _ | _ | _
  · exact Pos.cmp_lt_trans h1 e
  · rw [(Pos.cmp_eq_iff _ _).1 e] at h1; exact h1
  · exact absurd e h2

theorem Pos.lt_of_le_lt {p q r : Pos} (h1 : p.cmp q ≠ .gt) (h2 : q.cmp r = .lt) : p.cmp r = .lt := by
  rcases e : p.cmp q with _ | _ | _
  · exact Pos.cmp_lt_trans e h2
  · rw [(Pos.cmp_eq_iff _ _).1 e]; exact h2
  · exact absurd e h1

/-- Bounds strictly ascending. -/
def StrictB (b : Array Pos) : Prop :=
  ∀ i j (hi : i < b.size) (hj : j < b.size), i < j → b[i].cmp b[j] = .lt

theorem StrictB.le {b : Array Pos} (h : StrictB b) {i j : Nat} (hi : i < b.size) (hj : j < b.size)
    (hij : i ≤ j) : b[i].cmp b[j] ≠ .gt := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · rw [h i j hi hj hlt]; simp
  · rw [Pos.cmp_self]; simp

theorem StrictB.gt {b : Array Pos} (h : StrictB b) {i j : Nat} (hi : i < b.size) (hj : j < b.size)
    (hij : j < i) : b[i].cmp b[j] = .gt := Pos.lt_swap (h j i hj hi hij)

/-! ## The binary search -/

section
variable {m : Type → Type}

theorem getD_pos {b : Array Pos} {i : Nat} (h : i < b.size) : b.getD i default = b[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

/-- The search, where code runs. -/
theorem rankM_id (b : Array Pos) (p : Pos) (lo hi : Nat) :
    (rankM (m := _root_.Id) b p lo hi) =
      if lo < hi then
        (if (b.getD ((lo + hi) / 2) default).cmp p == .lt then rankM (m := _root_.Id) b p ((lo + hi) / 2 + 1) hi
        else rankM (m := _root_.Id) b p lo ((lo + hi) / 2))
      else pure lo := by
  rw [rankM]
  by_cases h : lo < hi
  · rw [dif_pos h, if_pos h]; rfl
  · rw [dif_neg h, if_neg h]

/-- **The search counts the bounds before p.** -/
theorem rank_spec {b : Array Pos} (hb : StrictB b) (p : Pos) :
    ∀ n lo hi, hi - lo = n → lo ≤ hi → hi ≤ b.size →
      (∀ j (hj : j < b.size), j < lo → b[j].cmp p = .lt) →
      (∀ j (hj : j < b.size), hi ≤ j → b[j].cmp p ≠ .lt) →
      let r := Id.run (rankM (m := _root_.Id) b p lo hi)
      lo ≤ r ∧ r ≤ hi ∧ (∀ j (hj : j < b.size), j < r → b[j].cmp p = .lt) ∧
        (∀ j (hj : j < b.size), r ≤ j → b[j].cmp p ≠ .lt) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn hle hsz hlo hhi
  simp only
  rw [rankM_id]
  by_cases h : lo < hi
  · rw [if_pos h]
    have hmid : (lo + hi) / 2 < b.size := by omega
    rw [getD_pos hmid]
    by_cases hc : b[(lo + hi) / 2].cmp p = .lt
    · rw [if_pos (by simp [hc])]
      have := ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl (by omega) hsz
        (fun j hj hjl => by
          rcases Nat.lt_or_ge j ((lo + hi) / 2) with hj' | hj'
          · exact Pos.cmp_lt_trans (hb j _ hj hmid hj') hc
          · have : j = (lo + hi) / 2 := by omega
            subst this; exact hc) hhi
      obtain ⟨a, b', c, d⟩ := this
      exact ⟨by omega, b', c, d⟩
    · rw [if_neg (by simp [hc])]
      have := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega) (by omega) hlo
        (fun j hj hjl => by
          rcases Nat.lt_or_eq_of_le hjl with hj' | rfl
          · intro hjp
            exact hc (Pos.cmp_lt_trans (hb _ j hmid hj hj') hjp)
          · exact hc)
      obtain ⟨a, b', c, d⟩ := this
      exact ⟨a, by omega, c, d⟩
  · rw [if_neg h]
    have : lo = hi := by omega
    subst this
    exact ⟨Nat.le_refl _, Nat.le_refl _, hlo, hhi⟩

end

/-! ## Building a key's bounds -/

theorem posLe_trans (a b c : Pos) (h1 : posLe a b = true) (h2 : posLe b c = true) : posLe a c = true := by
  simp only [posLe, bne_iff_ne, ne_eq] at *
  exact Pos.cmp_trans h1 h2

theorem posLe_total (a b : Pos) : (posLe a b || posLe b a) = true := by
  simp only [posLe, Bool.or_eq_true, bne_iff_ne, ne_eq]
  rw [Pos.cmp_swap a b]
  cases a.cmp b <;> simp

theorem mem_dedupSorted {x : Pos} : ∀ {l : List Pos}, x ∈ dedupSorted l ↔ x ∈ l
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | a :: b :: t => by
    unfold dedupSorted
    split
    · rename_i h
      have hab : a = b := (Pos.cmp_eq_iff a b).1 (by simpa using h)
      subst hab
      rw [mem_dedupSorted]
      simp
    · rw [List.mem_cons, mem_dedupSorted, List.mem_cons (l := b :: t)]

theorem dedupSorted_strict : ∀ {l : List Pos}, l.Pairwise (fun a b => posLe a b = true) →
    (dedupSorted l).Pairwise (fun a b => a.cmp b = .lt)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    unfold dedupSorted
    have h' := h
    rw [List.pairwise_cons] at h'
    split
    · exact dedupSorted_strict h'.2
    · rename_i hne
      refine List.pairwise_cons.2 ⟨fun c hc => ?_, dedupSorted_strict h'.2⟩
      have hab : a.cmp b ≠ .eq := by simpa using hne
      have hc' := mem_dedupSorted.1 hc
      have hac : a.cmp c ≠ .gt := by
        have := h'.1 c hc'; simpa [posLe] using this
      have hle : a.cmp b ≠ .gt := by
        have := h'.1 b (List.mem_cons_self ..); simpa [posLe] using this
      rcases List.mem_cons.1 hc' with rfl | hct
      · exact strict_of hle fun e => hab ((Pos.cmp_eq_iff _ _).2 e)
      · have hbc : b.cmp c ≠ .gt := by
          have := (List.pairwise_cons.1 h'.2).1 c hct; simpa [posLe] using this
        exact Pos.lt_of_lt_le (strict_of hle fun e => hab ((Pos.cmp_eq_iff _ _).2 e)) hbc

/-- The bounds of a set of windows. -/
def boundsOf {S : Type} (ws : Array (S × Win)) : Array Pos :=
  (dedupSorted ((endsOf ws).mergeSort posLe)).toArray

theorem build_bounds {S : Type} (ws : Array (S × Win)) : (Slots.build ws).bounds = boundsOf ws := rfl

theorem strictB_boundsOf {S : Type} (ws : Array (S × Win)) : StrictB (boundsOf ws) := by
  have hl := dedupSorted_strict (List.pairwise_mergeSort posLe_trans posLe_total (endsOf ws))
  have hl' : (boundsOf ws).toList.Pairwise (fun a b => a.cmp b = .lt) := by simpa [boundsOf] using hl
  intro i j hi hj hij
  have := (List.pairwise_iff_getElem.1 hl') i j (by simpa using hi) (by simpa using hj) hij
  simpa using this

theorem mem_boundsOf {S : Type} {ws : Array (S × Win)} {q : Pos} :
    q ∈ (boundsOf ws).toList ↔ q ∈ endsOf ws := by
  simp [boundsOf, mem_dedupSorted, List.mem_mergeSort]

/-- Every end of a window of ws is one of their bounds. -/
theorem end_bound {S : Type} {ws : Array (S × Win)} {x : S} {w : Win} (hw : (x, w) ∈ ws) {q : Pos}
    (hq : (∃ i, w.lo = some (q, i)) ∨ (∃ i, w.hi = some (q, i))) :
    ∃ j, ∃ hj : j < (boundsOf ws).size, (boundsOf ws)[j] = q := by
  have : q ∈ endsOf ws := by
    unfold endsOf
    rw [List.mem_flatMap]
    refine ⟨(x, w), Array.mem_toList_iff.2 hw, ?_⟩
    rcases hq with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp [hi]
    · simp [hi]
  have := mem_boundsOf.2 this
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem this
  exact ⟨j, by simpa using hj, by simpa using e⟩

/-! ## A gap's windows -/

section
variable {b : Array Pos} {i : Nat} {p : Pos}

/-- In gap i: p after the first i bounds and before the rest. -/
def InGap (b : Array Pos) (i : Nat) (p : Pos) : Prop :=
  i ≤ b.size ∧ (∀ j (hj : j < b.size), j < i → b[j].cmp p = .lt) ∧
    (∀ j (hj : j < b.size), i ≤ j → b[j].cmp p = .gt)

theorem gapLo_eq (hb : StrictB b) (hg : InGap b i p) {lo : Option End}
    (hq : ∀ q c, lo = some (q, c) → ∃ j, ∃ hj : j < b.size, b[j] = q) :
    gapLo b i lo = above lo p := by
  cases lo with
  | none => rfl
  | some e =>
    obtain ⟨q, c⟩ := e
    obtain ⟨j, hj, rfl⟩ := hq q c rfl
    obtain ⟨hi, hbef, haft⟩ := hg
    simp only [gapLo, above]
    by_cases hji : j < i
    · have hp : p.cmp b[j] = .gt := Pos.lt_swap (hbef j hj hji)
      rw [hp]
      have hi1 : i - 1 < b.size := by omega
      rw [getD_pos hi1]
      have := hb.le hj hi1 (by omega : j ≤ i - 1)
      simp [show 0 < i by omega, this]
    · have hp : p.cmp b[j] = .lt := Pos.gt_swap (haft j hj (by omega))
      rw [hp]
      by_cases hi0 : i = 0
      · simp [hi0]
      · have hi1 : i - 1 < b.size := by omega
        rw [getD_pos hi1, hb.gt hj hi1 (by omega)]
        simp

theorem gapHi_eq (hb : StrictB b) (hg : InGap b i p) {hi : Option End}
    (hq : ∀ q c, hi = some (q, c) → ∃ j, ∃ hj : j < b.size, b[j] = q) :
    gapHi b i hi = below hi p := by
  cases hi with
  | none => rfl
  | some e =>
    obtain ⟨q, c⟩ := e
    obtain ⟨j, hj, rfl⟩ := hq q c rfl
    obtain ⟨hsz, hbef, haft⟩ := hg
    simp only [gapHi, below]
    by_cases hji : j < i
    · have hp : p.cmp b[j] = .gt := Pos.lt_swap (hbef j hj hji)
      rw [hp]
      by_cases his : i < b.size
      · rw [getD_pos his, hb.gt his hj hji]; simp
      · simp [his]
    · have hp : p.cmp b[j] = .lt := Pos.gt_swap (haft j hj (by omega))
      rw [hp]
      have his : i < b.size := by omega
      rw [getD_pos his]
      have := hb.le his hj (by omega : i ≤ j)
      simp [his, this]

end

/-! ## A key's slots find exactly its windows that hold p -/

theorem mem_cover {S : Type} {ws : Array (S × Win)} {j : Nat} (hj : j < 2 * (boundsOf ws).size + 1) {x : S} :
    x ∈ (Slots.build ws).cover.getD j #[] ↔ ∃ w, (x, w) ∈ ws ∧ covers (boundsOf ws) j w = true := by
  simp only [Slots.build]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (by simpa [boundsOf] using hj),
    Option.getD_some, Array.mem_map]
  constructor
  · rintro ⟨⟨x', w⟩, h, rfl⟩
    rw [Array.mem_filter] at h
    exact ⟨w, h.1, h.2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨(x, w), Array.mem_filter.2 ⟨h1, h2⟩, rfl⟩

/-- **A key's slots find exactly the windows whose range holds p.** -/
theorem find_build {S : Type} (ws : Array (S × Win)) (p : Pos) (x : S) :
    x ∈ Id.run ((Slots.build ws).find p) ↔ ∃ w, (x, w) ∈ ws ∧ w.inside p = true := by
  have hb := strictB_boundsOf ws
  obtain ⟨hl, hr, hbef, haft⟩ := rank_spec hb p _ 0 (boundsOf ws).size rfl (Nat.zero_le _) (Nat.le_refl _)
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun j hj h => absurd hj (by omega))
  show x ∈ (Slots.build ws).cover.getD (slotOf (boundsOf ws) p
    (Id.run (rankM (m := _root_.Id) (boundsOf ws) p 0 (boundsOf ws).size))) #[] ↔ _
  generalize Id.run (rankM (m := _root_.Id) (boundsOf ws) p 0 (boundsOf ws).size) = i at hr hbef haft ⊢
  unfold slotOf
  by_cases hp : i < (boundsOf ws).size ∧ ((boundsOf ws).getD i default).cmp p = .eq
  · rw [if_pos (by have := hp.2; rw [getD_pos hp.1] at this; simp [hp.1, this])]
    rw [mem_cover (by omega)]
    have hpe : (boundsOf ws).getD i default = p := (Pos.cmp_eq_iff _ _).1 hp.2
    have hc : ∀ w, covers (boundsOf ws) (2 * i + 1) w = w.inside p := by
      intro w
      simp only [covers]
      rw [if_pos (by omega), show (2 * i + 1) / 2 = i by omega, hpe]
    simp only [hc]
  · rw [if_neg (by simpa using hp)]
    rw [mem_cover (by omega)]
    have hg : InGap (boundsOf ws) i p := by
      refine ⟨hr, hbef, fun j hj hij => ?_⟩
      have hn := haft j hj hij
      rcases Nat.lt_or_eq_of_le hij with hlt | rfl
      · have h1 := haft i (by omega) (Nat.le_refl _)
        have h2 := hb i j (by omega) hj hlt
        rcases e : (boundsOf ws)[i].cmp p with _ | _ | _
        · exact absurd e h1
        · rw [(Pos.cmp_eq_iff _ _).1 e] at h2; exact Pos.lt_swap h2
        · exact Pos.lt_swap (Pos.cmp_lt_trans (Pos.gt_swap e) h2)
      · rcases e : (boundsOf ws)[i].cmp p with _ | _ | _
        · exact absurd e hn
        · exact absurd ⟨hj, by rw [getD_pos hj]; exact e⟩ hp
        · rfl
    have hc : ∀ w, (∃ x, (x, w) ∈ ws) → covers (boundsOf ws) (2 * i) w = w.inside p := by
      rintro w ⟨x', hw⟩
      simp only [covers, Win.inside]
      rw [if_neg (by omega), show 2 * i / 2 = i by omega,
        gapLo_eq hb hg fun q c h => end_bound hw (Or.inl ⟨c, h⟩),
        gapHi_eq hb hg fun q c h => end_bound hw (Or.inr ⟨c, h⟩)]
    constructor
    · rintro ⟨w, hw, hcv⟩; exact ⟨w, hw, (hc w ⟨x, hw⟩) ▸ hcv⟩
    · rintro ⟨w, hw, hin⟩; exact ⟨w, hw, (hc w ⟨x, hw⟩).symm ▸ hin⟩

/-! ## The subscriptions -/

namespace Subs
variable {S : Type}

/-- Well formed: each key's slots are built from its windows, all under
that key. -/
def WF (I : Subs S) : Prop :=
  ∀ (k : ByteArray) (e : Array (S × Win) × Slots S), I.keys[k]? = some e →
    e.2 = Slots.build e.1 ∧ ∀ y ∈ e.1, y.2.key = k

/-- x subscribes to window w. -/
def Has (I : Subs S) (x : S) (w : Win) : Prop := (x, w) ∈ I.at_ w.key

theorem wf_empty : WF ({} : Subs S) := by
  intro k e h; simp [Std.HashMap.getElem?_empty] at h

theorem at_eq {I : Subs S} {k : ByteArray} : I.at_ k = ((I.keys[k]?).map (·.1)).getD #[] := rfl

/-- **The subscriptions find exactly the subscribers with a window
holding a row filed under k at p.** -/
theorem find_iff {I : Subs S} (hI : I.WF) (k : ByteArray) (p : Pos) (x : S) :
    x ∈ Id.run (I.find k p) ↔ ∃ w, I.Has x w ∧ w.has k p = true := by
  have e : Id.run (I.find k p) =
      (match I.keys[k]? with | none => #[] | some (_, sl) => Id.run (sl.find p)) := by
    simp only [find]; cases I.keys[k]? <;> rfl
  rw [e]
  cases he : I.keys[k]? with
  | none =>
    simp only
    constructor
    · intro h; simp at h
    · rintro ⟨w, hw, hk⟩
      simp only [Win.has, Bool.and_eq_true, decide_eq_true_eq] at hk
      simp only [Has, at_eq, ← hk.1, he] at hw
      simp at hw
  | some e =>
    obtain ⟨ws, sl⟩ := e
    obtain ⟨hsl, hkeys⟩ := hI k _ he
    simp only at hsl hkeys
    subst hsl
    show x ∈ Id.run ((Slots.build ws).find p) ↔ _
    rw [find_build]
    constructor
    · rintro ⟨w, hw, hin⟩
      have hk := hkeys _ hw
      simp only at hk
      refine ⟨w, ?_, ?_⟩
      · simp only [Has, at_eq, hk, he]; exact hw
      · simp [Win.has, hk, hin]
    · rintro ⟨w, hw, hk⟩
      simp only [Win.has, Bool.and_eq_true, decide_eq_true_eq] at hk
      simp only [Has, at_eq, ← hk.1, he] at hw
      exact ⟨w, hw, hk.2⟩

theorem set_wf {I : Subs S} (hI : I.WF) (k : ByteArray) (ws : Array (S × Win))
    (hk : ∀ y ∈ ws, y.2.key = k) : (I.set k ws).WF := by
  intro k' e he
  unfold set at he
  split at he
  · simp only [Std.HashMap.getElem?_erase] at he
    split at he
    · cases he
    · exact hI k' e he
  · simp only [Std.HashMap.getElem?_insert] at he
    split at he
    · rename_i hkk
      have : k = k' := eq_of_beq hkk
      subst this
      cases he
      exact ⟨rfl, hk⟩
    · exact hI k' e he

theorem at_set {I : Subs S} (k k' : ByteArray) (ws : Array (S × Win)) :
    (I.set k ws).at_ k' = if k = k' then ws else I.at_ k' := by
  unfold set
  split
  · rename_i hws
    simp only [at_eq, Std.HashMap.getElem?_erase]
    by_cases h : k = k'
    · subst h; simp; exact Array.isEmpty_iff.1 hws
    · simp [h]
  · simp only [at_eq, Std.HashMap.getElem?_insert]
    by_cases h : k = k'
    · subst h; simp
    · simp [h]

theorem at_wf {I : Subs S} (hI : I.WF) {k : ByteArray} {y : S × Win} (hy : y ∈ I.at_ k) : y.2.key = k := by
  rw [at_eq] at hy
  cases he : I.keys[k]? with
  | none => rw [he] at hy; simp at hy
  | some e => rw [he] at hy; exact (hI k e he).2 y hy

theorem add_wf {I : Subs S} (hI : I.WF) (x : S) (w : Win) : (I.add x w).WF := by
  refine set_wf hI _ _ fun y hy => ?_
  rcases Array.mem_push.1 hy with hy | rfl
  · exact at_wf hI hy
  · rfl

theorem has_add {I : Subs S} (x : S) (w : Win) (y : S) (v : Win) :
    (I.add x w).Has y v ↔ I.Has y v ∨ (y = x ∧ v = w) := by
  unfold Has add
  rw [at_set]
  by_cases h : w.key = v.key
  · rw [if_pos h, Array.mem_push, h]
    constructor
    · rintro (h' | h')
      · exact Or.inl h'
      · cases h'; exact Or.inr ⟨rfl, rfl⟩
    · rintro (h' | ⟨rfl, rfl⟩)
      · exact Or.inl h'
      · exact Or.inr rfl
  · rw [if_neg h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨rfl, rfl⟩)
      · exact h'
      · exact absurd rfl h

theorem ofList_wf (l : List (S × Win)) : (ofList l).WF := by
  unfold ofList
  suffices ∀ (I : Subs S), I.WF → (l.foldl (fun I (x, w) => I.add x w) I).WF from this _ wf_empty
  induction l with
  | nil => intro I h; exact h
  | cons a t ih => intro I h; exact ih _ (add_wf h a.1 a.2)

/-- **Subscriptions from a list hold exactly the list.** -/
theorem has_ofList (l : List (S × Win)) (y : S) (v : Win) : (ofList l).Has y v ↔ (y, v) ∈ l := by
  unfold ofList
  suffices ∀ (I : Subs S), (l.foldl (fun I (x, w) => I.add x w) I).Has y v ↔ I.Has y v ∨ (y, v) ∈ l by
    rw [this]; simp [Has, at_eq, Std.HashMap.getElem?_empty]
  induction l with
  | nil => intro I; simp
  | cons a t ih =>
    intro I
    simp only [List.foldl_cons]
    rw [ih, has_add, List.mem_cons]
    constructor
    · rintro ((h | ⟨rfl, rfl⟩) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr h

theorem keep_get {I : Subs S} (want : S → Bool) (k : ByteArray) :
    (I.keep want).keys[k]? = (I.keys[k]?).bind fun e =>
      let ws := e.1.filter (want ·.1)
      if ws.isEmpty then none else if ws.size = e.1.size then some e else some (ws, Slots.build ws) := by
  simp only [keep, Std.HashMap.getElem?_filterMap, Std.HashMap.getKey_eq]
  cases I.keys[k]? <;> rfl

theorem filter_size_eq {α : Type} {p : α → Bool} {a : Array α} (h : (a.filter p).size = a.size) :
    a.filter p = a := by
  apply Array.toList_inj.1
  rw [Array.toList_filter]
  apply List.filter_eq_self.2
  intro x hx
  apply Classical.byContradiction
  intro hp
  have : (a.toList.filter p).length < a.toList.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨x, hx, by simpa using hp⟩
  rw [← Array.toList_filter, Array.length_toList, Array.length_toList] at this
  omega

theorem keep_wf {I : Subs S} (hI : I.WF) (want : S → Bool) : (I.keep want).WF := by
  intro k e he
  rw [keep_get] at he
  cases h0 : I.keys[k]? with
  | none => rw [h0] at he; cases he
  | some e0 =>
    rw [h0] at he
    obtain ⟨hb, hk⟩ := hI k e0 h0
    simp only [Option.bind_some] at he
    split at he
    · cases he
    · split at he
      · cases he; exact ⟨hb, hk⟩
      · cases he
        exact ⟨rfl, fun y hy => hk y (Array.mem_filter.1 hy).1⟩

/-- **Keeping holds exactly the wanted subscriptions.** -/
theorem has_keep {I : Subs S} (want : S → Bool) (y : S) (v : Win) :
    (I.keep want).Has y v ↔ I.Has y v ∧ want y = true := by
  unfold Has
  rw [at_eq, at_eq, keep_get]
  cases h0 : I.keys[v.key]? with
  | none => simp
  | some e0 =>
    simp only [Option.bind_some, Option.map_some, Option.getD_some]
    split
    · rename_i hem
      simp only [Option.map_none, Option.getD_none]
      constructor
      · intro h; simp at h
      · rintro ⟨h1, h2⟩
        have : (y, v) ∈ e0.1.filter (want ·.1) := Array.mem_filter.2 ⟨h1, h2⟩
        rw [Array.isEmpty_iff.1 hem] at this; simp at this
    · split
      · rename_i _ hsz
        simp only [Option.map_some, Option.getD_some]
        have := filter_size_eq hsz
        constructor
        · intro h; rw [← this] at h; exact ⟨by rw [← this]; exact h, (Array.mem_filter.1 h).2⟩
        · rintro ⟨h1, _⟩; exact h1
      · simp only [Option.map_some, Option.getD_some, Array.mem_filter]

/-- **Notified: exactly the subscribers with a window holding one of the
net filings.** -/
theorem mem_notifyM {I : Subs S} (hI : I.WF) (x : S) :
    ∀ (J : List (ByteArray × Pos)),
      x ∈ Id.run (I.notifyM J) ↔ ∃ e ∈ J, ∃ w, I.Has x w ∧ w.has e.1 e.2 = true
  | [] => by simp [notifyM]
  | (k, p) :: rest => by
    show x ∈ Id.run (I.find k p) ++ Id.run (I.notifyM rest) ↔ _
    rw [Array.mem_append, find_iff hI, mem_notifyM hI x rest]
    simp only [List.mem_cons, exists_eq_or_imp]

end Subs

/-! ## Netting -/

theorem contains_toggle (m : Std.HashMap (ByteArray × Pos) Unit) (e q : ByteArray × Pos) :
    (toggle m e).contains q = (m.contains q ^^ (e == q)) := by
  unfold toggle
  by_cases he : m.contains e = true
  · rw [if_pos he, Std.HashMap.contains_erase]
    by_cases hq : e = q
    · subst hq; rw [beq_self_eq_true, he]; rfl
    · rw [beq_eq_false_iff_ne.2 hq]; cases m.contains q <;> rfl
  · rw [if_neg he, Std.HashMap.contains_insert]
    by_cases hq : e = q
    · subst hq; simp only [Bool.not_eq_true] at he; rw [beq_self_eq_true, he]; rfl
    · rw [beq_eq_false_iff_ne.2 hq]; cases m.contains q <;> rfl

/-- How many of a journal's rows are at (k, p), mod 2, as a Bool. -/
def oddAt (J : List Filing) (q : ByteArray × Pos) : Bool :=
  J.countP (fun e => Decidable.decide (e.key = q.1 ∧ e.pos = q.2)) % 2 == 1

theorem contains_foldl : ∀ (J : List Filing) (m : Std.HashMap (ByteArray × Pos) Unit) (q : ByteArray × Pos),
    (J.foldl (fun m e => toggle m (e.key, e.pos)) m).contains q = (m.contains q ^^ oddAt J q)
  | [], m, q => by simp [oddAt]
  | e :: t, m, q => by
    rw [List.foldl_cons, contains_foldl t, contains_toggle]
    have : oddAt (e :: t) q = (((e.key, e.pos) == q) ^^ oddAt t q) := by
      simp only [oddAt, List.countP_cons]
      by_cases h : (e.key, e.pos) = q
      · subst h
        simp only [and_self, decide_true, ite_true, beq_self_eq_true]
        generalize List.countP _ t = n
        rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [Nat.add_mod, hn]
      · have h' : ¬ (e.key = q.1 ∧ e.pos = q.2) := fun ⟨a, b⟩ => h (Prod.ext a b)
        rw [beq_eq_false_iff_ne.2 h, Bool.false_xor]
        simp [h']
    rw [this, Bool.xor_assoc]

/-- **The net filings: the pairs a batch touched an odd number of times.** -/
theorem mem_net (J : Array Filing) (q : ByteArray × Pos) : q ∈ (net J).toList ↔ oddAt J.toList q = true := by
  unfold net
  rw [Array.mem_toList_iff, Std.HashMap.mem_keysArray, Std.HashMap.mem_iff_contains, ← Array.foldl_toList,
    contains_foldl]
  simp [Std.HashMap.contains_empty]

end Engine
