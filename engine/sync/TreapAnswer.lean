/-
The room's canonical Merkle treap, as sync runs it (Treap.lean has the
treap and its split and insert laws): a range's fingerprint is two
splits, an answer a few more, and every one is `answer`'s over the
room's items in key order, so `exchange_complete` and `exchange_log`
are about what runs.

- `toList_canon`: the canonical treap of sorted items holds them in
  order; `size_canon`: its size is their count.
- `rangeT_canon`: two splits of the room's treap at a range's ends give
  the canonical treap of the room's items in the range; so its size and
  label are the range's fingerprint (`fp`).
- `cutsT_canon`: the cuts read by rank off the sizes the nodes keep are
  `cutsOf`'s.
- `answerT_canon`, `openingT_canon`: **the treap's answer and opening
  are `answer`'s and `opening`'s**, over the room's sorted items.
- `rangeTM_hashes`: a range's tree costs at most twice the room tree's
  height in hashes; `answerTM_hashes`: an answer at most
  2·(fan + 1)·height, whatever the room holds.
-/
import engine.sync.Treap
import engine.sync.DepthLaws

namespace Engine.Sync

/-! ## In order, by rank, by key -/

namespace Treap
variable {α : Type}

/-- The items in key order (the in-order walk). -/
def toList : Treap α → List α
  | .leaf => []
  | .node l a r _ _ => l.toList ++ a :: r.toList

/-- The item at rank i, by the sizes the nodes keep. -/
def nth : Treap α → Nat → Option α
  | .leaf, _ => none
  | .node l a r _ _, i =>
    if i < l.size then l.nth i else if i = l.size then some a else r.nth (i - l.size - 1)

/-- Each node keeps its subtree's size. -/
def SizeOk : Treap α → Prop
  | .leaf => True
  | .node l _ r _ s => s = l.size + 1 + r.size ∧ SizeOk l ∧ SizeOk r

theorem size_toList : ∀ {t : Treap α}, SizeOk t → t.size = t.toList.length
  | .leaf, _ => rfl
  | .node l a r _ s, ⟨hs, hl, hr⟩ => by
    simp only [size, toList, List.length_append, List.length_cons]
    rw [hs, size_toList hl, size_toList hr]; omega

theorem nth_toList : ∀ {t : Treap α}, SizeOk t → ∀ i, t.nth i = t.toList[i]?
  | .leaf, _, i => by simp [nth, toList]
  | .node l a r _ s, ⟨_, hl, hr⟩, i => by
    have el := size_toList hl
    simp only [nth, toList]
    by_cases h1 : i < l.size
    · rw [if_pos h1, nth_toList hl i, List.getElem?_append_left (by omega)]
    · rw [if_neg h1]
      by_cases h2 : i = l.size
      · subst h2; rw [if_pos rfl, List.getElem?_append_right (by omega), el]; simp
      · rw [if_neg h2, nth_toList hr, List.getElem?_append_right (by omega),
          List.getElem?_cons]
        have : i - l.toList.length ≠ 0 := by omega
        rw [if_neg this, el]
        try (congr 1; omega)

end Treap

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray)

/-- Whether an item of key k is in the tree, searched down by key. -/
def Treap.hasKey (k : Key) : Treap α → Bool
  | .leaf => false
  | .node l a r _ _ => if k < key a then l.hasKey k else if key a < k then r.hasKey k else true

theorem mk_sizeOk {l r : Treap α} (a : α) (hl : l.SizeOk) (hr : r.SizeOk) :
    (Treap.mk ident h l a r).SizeOk := ⟨rfl, hl, hr⟩

theorem canon_sizeOk : ∀ (n : Nat) (l : List α), l.length ≤ n → (canon key ident h l).SizeOk := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [canon_eq]; simp [top, Treap.SizeOk]
  | succ n ih =>
    intro l hl
    rw [canon_eq]
    cases ht : top key l with
    | none => trivial
    | some t =>
      have h1 := below_lt key (top_mem key ht)
      have h2 := above_lt key (top_mem key ht)
      exact mk_sizeOk ident h t (ih _ (by omega)) (ih _ (by omega))

/-- In a sorted list, the items below one of its items, it, and the items
above are the list. -/
theorem sorted_split : ∀ {l : List α}, Sorted key l → ∀ {t : α}, t ∈ l →
    below key l t ++ t :: above key l t = l
  | [], _, _, ht => by cases ht
  | a :: u, hs, t, ht => by
    have hau := (List.pairwise_cons.1 hs).1
    have hu := (List.pairwise_cons.1 hs).2
    rcases List.mem_cons.1 ht with rfl | ht
    · have e1 : below key (t :: u) t = [] := by
        simp only [below, List.filter_cons, Key.lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
        exact List.filter_eq_nil_iff.2 fun b hb => by simp [Key.lt_asymm (hau b hb)]
      have e2 : above key (t :: u) t = u := by
        simp only [above, List.filter_cons, Key.lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
        exact List.filter_eq_self.2 fun b hb => by simp [hau b hb]
      rw [e1, e2]; rfl
    · have hat := hau t ht
      have e1 : below key (a :: u) t = a :: below key u t := by
        simp [below, List.filter_cons, hat]
      have e2 : above key (a :: u) t = above key u t := by
        simp [above, List.filter_cons, Key.lt_asymm hat]
      rw [e1, e2, List.cons_append, sorted_split hu ht]

/-- **The canonical treap of sorted items holds them in order.** -/
theorem toList_canon : ∀ (n : Nat) (l : List α), l.length ≤ n → Sorted key l →
    (canon key ident h l).toList = l := by
  intro n
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [canon_eq]; simp [top, Treap.toList]
  | succ n ih =>
    intro l hl hs
    rw [canon_eq]
    cases ht : top key l with
    | none => rw [(top_none key).1 ht]; rfl
    | some t =>
      have hm := top_mem key ht
      have h1 := below_lt key hm
      have h2 := above_lt key hm
      show (canon key ident h (below key l t)).toList ++ t :: (canon key ident h (above key l t)).toList = l
      rw [ih (below key l t) (by omega) (List.Pairwise.filter _ hs),
        ih (above key l t) (by omega) (List.Pairwise.filter _ hs)]
      exact sorted_split key hs hm

theorem toList_canon' {l : List α} (hs : Sorted key l) : (canon key ident h l).toList = l :=
  toList_canon key ident h _ l (Nat.le_refl _) hs

theorem canon_nil : canon key ident h ([] : List α) = .leaf := by
  rw [canon_eq]; simp [top]

/-- **Searching by key finds what the list holds.** -/
theorem hasKey_canon : ∀ (n : Nat) (l : List α), l.length ≤ n → Sorted key l → ∀ k,
    (canon key ident h l).hasKey key k = true ↔ ∃ b ∈ l, key b = k := by
  intro n
  induction n with
  | zero =>
    intro l hl _ k
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [canon_nil]; simp [Treap.hasKey]
  | succ n ih =>
    intro l hl hs k
    rw [canon_eq]
    cases ht : top key l with
    | none => rw [(top_none key).1 ht]; simp [Treap.hasKey]
    | some t =>
      have hm := top_mem key ht
      have h1 := below_lt key hm
      have h2 := above_lt key hm
      have e := sorted_split key hs hm
      show (Treap.node _ t _ _ _).hasKey key k = true ↔ _
      simp only [Treap.hasKey]
      have ib := ih (below key l t) (by omega) (List.Pairwise.filter _ hs) k
      have ia := ih (above key l t) (by omega) (List.Pairwise.filter _ hs) k
      have mb : ∀ b, b ∈ below key l t ↔ b ∈ l ∧ key b < key t := fun b => by simp [below]
      have ma : ∀ b, b ∈ above key l t ↔ b ∈ l ∧ key t < key b := fun b => by simp [above]
      split
      · rename_i hk
        rw [ib]
        constructor
        · rintro ⟨b, hb, rfl⟩; exact ⟨b, ((mb b).1 hb).1, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          refine ⟨b, (mb b).2 ⟨hb, ?_⟩, rfl⟩
          rcases Key.lt_trichotomy (key b) (key t) with h' | h' | h'
          · exact h'
          · exact absurd (h' ▸ hk) (Key.lt_irrefl _)
          · exact absurd (Key.lt_trans hk h') (Key.lt_irrefl _)
      · split
        · rename_i hk1 hk
          rw [ia]
          constructor
          · rintro ⟨b, hb, rfl⟩; exact ⟨b, ((ma b).1 hb).1, rfl⟩
          · rintro ⟨b, hb, rfl⟩
            refine ⟨b, (ma b).2 ⟨hb, ?_⟩, rfl⟩
            rcases Key.lt_trichotomy (key b) (key t) with h' | h' | h'
            · exact absurd (Key.lt_trans hk h') (Key.lt_irrefl _)
            · exact absurd (h' ▸ hk) (Key.lt_irrefl _)
            · exact h'
        · rename_i hk1 hk2
          simp only [true_iff]
          refine ⟨t, hm, ?_⟩
          rcases Key.lt_trichotomy (key t) k with h' | h' | h'
          · exact absurd h' hk2
          · exact h'
          · exact absurd h' hk1

theorem hasKey_canon' {l : List α} (hs : Sorted key l) (k : Key) :
    (canon key ident h l).hasKey key k = true ↔ ∃ b ∈ l, key b = k :=
  hasKey_canon key ident h _ l (Nat.le_refl _) hs k

/-- **The canonical treap is the set's**: any order of the same items,
no two sharing a key, has one. -/
theorem canon_perm : ∀ (n : Nat) (l l' : List α), l.length ≤ n → Untied key l → l.Perm l' →
    canon key ident h l = canon key ident h l' := by
  intro n
  induction n with
  | zero =>
    intro l l' hl _ hp
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [List.Perm.nil_eq hp]
  | succ n ih =>
    intro l l' hl hd hp
    rw [canon_eq key ident h l, canon_eq key ident h l', ← top_perm (key := key) hd hp]
    cases ht : top key l with
    | none => rfl
    | some m =>
      have hm := top_mem key ht
      have sub : ∀ (q : α → Bool), Untied key (l.filter q) :=
        fun q a ha b hb => hd a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1
      simp only
      rw [ih (below key l m) (below key l' m) (by have := below_lt key hm; omega) (sub _) (hp.filter _),
        ih (above key l m) (above key l' m) (by have := above_lt key hm; omega) (sub _) (hp.filter _)]

/-- Where the code runs, its value is what `Id.run` gives. -/
theorem run_eq_val {β : Type} (x : _root_.Id β) : _root_.Id.run x = Valued.val x := rfl

/-- **Its size is their count.** -/
theorem size_canon {l : List α} (hs : Sorted key l) : (canon key ident h l).size = l.length := by
  rw [Treap.size_toList (canon_sizeOk key ident h _ l (Nat.le_refl _)), toList_canon' key ident h hs]

end

/-! ## A range's tree: two splits -/

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray)

/-- The tree of the items in r: split at its start, then at its end. -/
def rangeT (r : Range) (t : Treap α) : Treap α :=
  match r.hi with
  | none => (t.split key ident h r.lo).2
  | some e => ((t.split key ident h r.lo).2.split key ident h e).1

/-- Sorted items are keyed apart, so no two share a priority. -/
theorem sorted_prio : ∀ {l : List α}, Sorted key l → Prio key l
  | [], _ => fun a ha => by cases ha
  | a :: u, hs => by
    have hau := (List.pairwise_cons.1 hs).1
    have hu := sorted_prio (List.pairwise_cons.1 hs).2
    intro x hx y hy e
    cases List.mem_cons.1 hx with
    | inl hxa =>
      cases List.mem_cons.1 hy with
      | inl hya => rw [hxa, hya]
      | inr hyu =>
        have := hau y hyu
        rw [← hxa, e] at this; exact absurd this (Key.lt_irrefl _)
    | inr hxu =>
      cases List.mem_cons.1 hy with
      | inl hya =>
        have := hau x hxu
        rw [← hya, ← e] at this; exact absurd this (Key.lt_irrefl _)
      | inr hyu => exact hu x hxu y hyu e

theorem prio_filter {l : List α} (hp : Prio key l) (q : α → Bool) : Prio key (l.filter q) :=
  fun a ha b hb => hp a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1

/-- **Two splits give the range's canonical treap.** -/
theorem rangeT_canon {l : List α} (hp : Prio key l) (r : Range) :
    rangeT key ident h r (canon key ident h l) = canon key ident h (within key r l) := by
  unfold rangeT
  rw [split_canon key ident h r.lo _ l (Nat.le_refl _) hp]
  cases hr : r.hi with
  | none =>
    dsimp only
    congr 1
    unfold highs within
    apply List.filter_congr; intro a _; simp [Range.has, hr]
  | some e =>
    dsimp only
    rw [split_canon key ident h e _ (highs key r.lo l) (Nat.le_refl _) (prio_filter key hp _)]
    dsimp only
    congr 1
    unfold lows highs within
    rw [List.filter_filter]
    apply List.filter_congr; intro a _; simp [Range.has, hr, Bool.and_comm]

end

/-! ## Cutting by rank -/

/-- The positions k, k + s, k + 2s, … below n, as `pick` takes them. -/
def steps (s : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | 0, n + 1 => 0 :: (steps s (s - 1) n).map (· + 1)
  | k + 1, n + 1 => (steps s k n).map (· + 1)

theorem pick_steps {α : Type} (s : Nat) : ∀ (k : Nat) (x : List α),
    pick s k x = (steps s k x.length).filterMap fun i => x[i]?
  | _, [] => by cases ‹Nat› <;> simp [pick, steps]
  | 0, a :: t => by
    simp only [pick, List.length_cons, steps, List.filterMap_cons, List.getElem?_cons_zero,
      List.filterMap_map]
    congr 1
    rw [pick_steps s (s - 1) t]
    first | (congr 1; done) | (congr 1; funext i; simp)
  | k + 1, a :: t => by
    simp only [pick, List.length_cons, steps, List.filterMap_map]
    rw [pick_steps s k t]
    first | (congr 1; done) | (congr 1; funext i; simp)

/-- How many positions k, k + s, … are below n. -/
def stepCount (s k n : Nat) : Nat := if k < n then (n - 1 - k) / s + 1 else 0

theorem steps_eq (s : Nat) (hs : 1 ≤ s) : ∀ (n k : Nat),
    steps s k n = (List.range (stepCount s k n)).map fun j => k + j * s
  | 0, k => by simp [steps, stepCount]
  | n + 1, 0 => by
    rw [steps, steps_eq s hs n (s - 1)]
    have hc : stepCount s 0 (n + 1) = stepCount s (s - 1) n + 1 := by
      unfold stepCount
      by_cases h1 : s - 1 < n
      · rw [if_pos (by omega), if_pos h1]
        have := Nat.div_eq_sub_div (a := n) (b := s) (by omega) (by omega)
        have e : n - 1 - (s - 1) = n - s := by omega
        rw [e]; simp only [Nat.sub_zero, Nat.add_sub_cancel]; omega
      · rw [if_pos (by omega), if_neg h1, Nat.div_eq_of_lt (by omega)]
    rw [hc, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left; intro j _; simp only [Function.comp]; rw [Nat.succ_mul]; omega
  | n + 1, k + 1 => by
    rw [steps, steps_eq s hs n k]
    have hc : stepCount s (k + 1) (n + 1) = stepCount s k n := by
      unfold stepCount
      by_cases h1 : k < n
      · rw [if_pos (by omega), if_pos h1]; congr 2; omega
      · rw [if_neg (by omega), if_neg h1]
    rw [hc, List.map_map]
    apply List.map_congr_left; intro j _; simp only [Function.comp]; omega

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- Where a range's tree is cut: at every `runLen`-th item, each read by
rank off the sizes its nodes keep (at most `fan` reads). -/
def cutsT (t : Treap α) : List Key :=
  let s := runLen P t.size
  (((List.range (stepCount s s t.size)).map fun j => s + j * s).filterMap t.nth).map key

theorem runLen_pos {n : Nat} (hn : 1 ≤ n) : 1 ≤ runLen P n := by
  unfold runLen
  have := P.fan_two
  exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)

/-- **The cuts read by rank are `cutsOf`'s.** -/
theorem cutsT_canon {x : List α} (hs : Sorted key x) (hn : 1 ≤ x.length) :
    cutsT key P (canon key ident h x) = cutsOf key P x := by
  unfold cutsT cutsOf
  dsimp only
  have hok := canon_sizeOk key ident h _ x (Nat.le_refl _)
  have hnth : (canon key ident h x).nth = fun i => x[i]? := by
    funext i; rw [Treap.nth_toList hok, toList_canon' key ident h hs]
  rw [size_canon key ident h hs, pick_steps, steps_eq _ (runLen_pos P hn), hnth]

end

/-! ## Answering from the room's tree -/

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- What this side answers to a claim, from its room's tree `root`. -/
def answerT (root : Treap α) : Claim → List Out
  | .fp r n l =>
    let t := rangeT key ident h r root
    if (t.size, t.label h) = (n, l) then []
    else if t.size ≤ P.leaf then [.claim (.ids r (t.toList.map ident))]
    else (pieces r (cutsT key P t)).map fun q =>
      let u := rangeT key ident h q root
      .claim (.fp q u.size (u.label h))
  | .ids r xs =>
    let x := (rangeT key ident h r root).toList
    [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident),
     .want (xs.filter fun i => !named ident x i)]

/-- How this side opens a round over r, from its room's tree. -/
def openingT (root : Treap α) (r : Range) : Claim :=
  let t := rangeT key ident h r root
  if t.size ≤ P.leaf then .ids r (t.toList.map ident) else .fp r t.size (t.label h)

theorem fp_canon {l : List α} (hs : Sorted key l) (r : Range) :
    ((rangeT key ident h r (canon key ident h l)).size, (rangeT key ident h r (canon key ident h l)).label h) =
      fp key ident h (within key r l) := by
  have hw : Sorted key (within key r l) := List.Pairwise.filter _ hs
  rw [rangeT_canon key ident h (sorted_prio key hs), size_canon key ident h hw,
    label_canon key ident h _ _ (Nat.le_refl _)]
  rfl

/-- **The treap's answer is `answer`'s** over the room's sorted items. -/
theorem answerT_canon {l : List α} (hs : Sorted key l) (c : Claim) :
    answerT key ident h P (canon key ident h l) c = answer key ident h P l c := by
  have hp := sorted_prio key hs
  have hw : ∀ r, Sorted key (within key r l) := fun _ => List.Pairwise.filter _ hs
  cases c with
  | fp r n lb =>
    simp only [answerT, answer]
    rw [fp_canon key ident h hs r, rangeT_canon key ident h hp r, size_canon key ident h (hw r),
      toList_canon' key ident h (hw r)]
    split
    · rfl
    · split
      · rfl
      · rename_i hle
        rw [cutsT_canon key ident h P (hw r) (by omega)]
        apply List.map_congr_left; intro q _
        rw [← fp_canon key ident h hs q]
  | ids r xs =>
    simp only [answerT, answer]
    rw [rangeT_canon key ident h hp r, toList_canon' key ident h (hw r)]

/-- **The treap's opening is `opening`'s.** -/
theorem openingT_canon {l : List α} (hs : Sorted key l) (r : Range) :
    openingT key ident h P (canon key ident h l) r = opening key ident h P l r := by
  have hw : Sorted key (within key r l) := List.Pairwise.filter _ hs
  simp only [openingT, opening]
  rw [rangeT_canon key ident h (sorted_prio key hs) r, size_canon key ident h hw,
    toList_canon' key ident h hw, label_canon key ident h _ _ (Nat.le_refl _)]
  rfl

end

/-! ## As it runs, counted -/

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)
variable {m : Type → Type} [Monad m] [Tick m]

/-- `rangeT`, as it runs: two splits, each through the hash's door. -/
def rangeTM (r : Range) (t : Treap α) : m (Treap α) := do
  let p ← t.splitM key ident h r.lo
  match r.hi with
  | none => pure p.2
  | some e => do
    let q ← p.2.splitM key ident h e
    pure q.1

/-- Each piece claimed by its range's size and label. -/
def piecesTM (root : Treap α) : List Range → m (List Out)
  | [] => pure []
  | q :: qs => do
    let u ← rangeTM key ident h q root
    let rest ← piecesTM root qs
    pure (.claim (.fp q u.size (u.label h)) :: rest)

/-- `answerT`, as it runs. -/
def answerTM (root : Treap α) : Claim → m (List Out)
  | .fp r n l => do
    let t ← rangeTM key ident h r root
    if (t.size, t.label h) = (n, l) then pure []
    else if t.size ≤ P.leaf then pure [.claim (.ids r (t.toList.map ident))]
    else piecesTM key ident h root (pieces r (cutsT key P t))
  | .ids r xs => do
    let t ← rangeTM key ident h r root
    let x := t.toList
    pure [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident),
      .want (xs.filter fun i => !named ident x i)]

/-- `openingT`, as it runs. -/
def openingTM (root : Treap α) (r : Range) : m Claim := do
  let t ← rangeTM key ident h r root
  pure (if t.size ≤ P.leaf then .ids r (t.toList.map ident) else .fp r t.size (t.label h))

end

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}
variable {m : Type → Type} [Monad m] [Tick m] [Valued m]
open Valued

theorem val_rangeTM (r : Range) (t : Treap α) :
    val (rangeTM (m := m) key ident h r t) = rangeT key ident h r t := by
  unfold rangeTM rangeT
  cases r.hi <;> simp [val_splitM]

theorem val_piecesTM (root : Treap α) : ∀ qs : List Range,
    val (piecesTM (m := m) key ident h root qs) =
      qs.map fun q => .claim (.fp q (rangeT key ident h q root).size ((rangeT key ident h q root).label h))
  | [] => by simp [piecesTM]
  | q :: qs => by simp [piecesTM, val_rangeTM, val_piecesTM root qs]

/-- **What runs answers as `answerT` does.** -/
theorem val_answerTM (root : Treap α) (c : Claim) :
    val (answerTM (m := m) key ident h P root c) = answerT key ident h P root c := by
  cases c with
  | fp r n l =>
    simp only [answerTM, answerT, val_bind, val_rangeTM]
    split
    · simp
    · split
      · simp
      · rw [val_piecesTM]
  | ids r xs => simp [answerTM, answerT, val_rangeTM]

theorem val_openingTM (root : Treap α) (r : Range) :
    val (openingTM (m := m) key ident h P root r) = openingT key ident h P root r := by
  simp [openingTM, openingT, val_rangeTM]

end

/-! ## What it costs -/

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- A split's halves are no higher than the tree. -/
theorem split_height (k : Key) : ∀ t : Treap α,
    (t.split key ident h k).1.height ≤ t.height ∧ (t.split key ident h k).2.height ≤ t.height
  | .leaf => by simp [Treap.split]
  | .node l a r _ _ => by
    unfold Treap.split
    split
    · have := split_height k r
      simp only [Treap.mk, Treap.height] at *; omega
    · have := split_height k l
      simp only [Treap.mk, Treap.height] at *; omega

open Counted in
/-- **A range's tree costs at most twice the tree's height in hashes.** -/
theorem rangeTM_hashes (r : Range) (t : Treap α) :
    (cost (rangeTM (m := Counted) key ident h r t)).hashes ≤ 2 * t.height := by
  unfold rangeTM
  have h1 := split_hashes key ident h r.lo t
  have hv : Counted.val (t.splitM (m := Counted) key ident h r.lo) = t.split key ident h r.lo :=
    val_splitM (m := Counted) key ident h r.lo t
  cases r.hi with
  | none => simp only [cost_bind, cost_pure, Meter.hashes_add, Meter.hashes_zero]; omega
  | some e =>
    have h2 := split_hashes key ident h e (Counted.val (t.splitM (m := Counted) key ident h r.lo)).2
    have h3 := (split_height key ident h r.lo t).2
    rw [hv] at h2
    simp only [cost_bind, cost_pure, Meter.hashes_add, Meter.hashes_zero, hv]
    omega

open Counted in
theorem piecesTM_hashes (root : Treap α) : ∀ qs : List Range,
    (cost (piecesTM (m := Counted) key ident h root qs)).hashes ≤ qs.length * (2 * root.height)
  | [] => by simp [piecesTM]
  | q :: qs => by
    have := rangeTM_hashes key ident h q root
    have := piecesTM_hashes root qs
    simp only [piecesTM, cost_bind, cost_pure, Meter.hashes_add, Meter.hashes_zero, List.length_cons]
    rw [Nat.succ_mul]; omega

/-- A cut makes at most `fan` pieces, whatever the tree. -/
theorem cutsT_pieces (r : Range) (t : Treap α) : (pieces r (cutsT key P t)).length ≤ P.fan := by
  rw [pieces_len]
  unfold cutsT
  simp only [List.length_map]
  have hf := P.fan_two
  generalize t.size = n
  have hle : ∀ l : List Nat, (l.filterMap t.nth).length ≤ l.length := fun l => List.length_filterMap_le _ _
  refine Nat.le_trans (Nat.add_le_add_right (hle _) 1) ?_
  simp only [List.length_map, List.length_range]
  unfold stepCount
  split
  · rename_i hsn
    have hs : 1 ≤ runLen P n := runLen_pos P (by omega)
    have hc : n ≤ runLen P n * P.fan := div_ceil_mul n P.fan (by omega)
    generalize runLen P n = s at hs hsn hc
    have : (n - 1 - s) / s + 1 = (n - 1) / s := by
      rw [Nat.div_eq_sub_div (a := n - 1) (b := s) (by omega) (by omega)]
    rw [this]
    have hc' : n ≤ P.fan * s := by rw [Nat.mul_comm]; exact hc
    have : (n - 1) / s < P.fan := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega
  · omega

open Counted in
/-- **An answer costs at most 2·(fan + 1)·height hashes**, whatever the
room holds: the claim's range, then each of at most `fan` pieces. -/
theorem answerTM_hashes (root : Treap α) (c : Claim) :
    (cost (answerTM (m := Counted) key ident h P root c)).hashes ≤ 2 * (P.fan + 1) * root.height := by
  have hr : ∀ r, (cost (rangeTM (m := Counted) key ident h r root)).hashes ≤ 2 * root.height :=
    fun r => rangeTM_hashes key ident h r root
  cases c with
  | fp r n l =>
    simp only [answerTM, cost_bind]
    have := hr r
    have h2 : 2 * root.height ≤ 2 * (P.fan + 1) * root.height :=
      Nat.mul_le_mul_right _ (by omega)
    split
    · simp only [cost_pure, Meter.hashes_add, Meter.hashes_zero]; omega
    · split
      · simp only [cost_pure, Meter.hashes_add, Meter.hashes_zero]; omega
      · have hp := piecesTM_hashes key ident h root
          (pieces r (cutsT key P (Counted.val (rangeTM (m := Counted) key ident h r root))))
        have hc := cutsT_pieces key P r (Counted.val (rangeTM (m := Counted) key ident h r root))
        simp only [Meter.hashes_add]
        have : (pieces r (cutsT key P (Counted.val (rangeTM (m := Counted) key ident h r root)))).length *
            (2 * root.height) ≤ P.fan * (2 * root.height) := Nat.mul_le_mul_right _ hc
        have e : 2 * (P.fan + 1) * root.height = 2 * root.height + P.fan * (2 * root.height) := by
          rw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_comm 2 P.fan, Nat.mul_assoc, Nat.add_comm]
        omega
  | ids r xs =>
    simp only [answerTM, cost_bind, cost_pure, Meter.hashes_add, Meter.hashes_zero]
    have := hr r
    have : 2 * root.height ≤ 2 * (P.fan + 1) * root.height := Nat.mul_le_mul_right _ (by omega)
    omega

open Counted in
theorem openingTM_hashes (root : Treap α) (r : Range) :
    (cost (openingTM (m := Counted) key ident h P root r)).hashes ≤ 2 * root.height := by
  simp only [openingTM, cost_bind, cost_pure, Meter.hashes_add, Meter.hashes_zero]
  have := rangeTM_hashes key ident h r root
  omega

end

end Engine.Sync
