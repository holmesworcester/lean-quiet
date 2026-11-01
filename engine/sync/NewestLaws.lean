/-
Newest first (docs/SYNC.md, "Windows and order"). The holder orders
what it offers, since the side that lacks ops cannot sort ids it does not
hold, and the peer wants and is served them in that order (`onHold`
keeps a have's order; the serve queue is FIFO).

- `answer_newest_first`: from its items in key order, an answer claims
  its pieces newest first, and every list of ids it sends (a have, or an
  ids claim) is its items in the claim's range, newest first.
- `window_first`: a window is the structure range (time 0, which
  everything else needs) and then claimed times, in that order.
- `newest_first`: a round's message, answering claims that come
  structure first and then newest first (an opening over a window, or
  an answer's pieces), sends its haves in that order: structure first,
  then the newest.
-/
import engine.sync.RoundLaws
import engine.sync.Conn

namespace Engine.Sync

/-- k comes before k' in sync's order: structure (time 0) first, then
the newest first. -/
def first (k k' : Key) : Prop := (k.t = 0 ∧ k'.t ≠ 0) ∨ ((k.t = 0 ↔ k'.t = 0) ∧ k' < k)

/-- Every key of q comes before every key of q'. -/
def Range.Before (q q' : Range) : Prop := ∀ k k', q.has k = true → q'.has k' = true → first k k'

/-- Every key of q' is below every key of q. -/
def Range.Above (q q' : Range) : Prop := ∀ k k', q.has k = true → q'.has k' = true → k' < k

/-- A range of one class: only structure, or only claimed times. -/
def Range.Plain (q : Range) : Prop := ∀ k k', q.has k = true → q.has k' = true → (k.t = 0 ↔ k'.t = 0)

/-- The ids of a have, or none. -/
def holdIds : Out → List ByteArray
  | .hold xs => xs
  | _ => []

/-- The range a claim is about. -/
def Claim.range : Claim → Range
  | .fp r _ _ => r
  | .ids r _ => r

/-- The ranges of the claims among outputs, in order. -/
def claimRanges (os : List Out) : List Range :=
  os.filterMap fun | .claim d => some d.range | _ => none

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

theorem pick_sublist (s : Nat) : ∀ (k : Nat) (l : List α), (pick s k l).Sublist l
  | _, [] => by simp [pick]
  | 0, a :: t => by simp only [pick]; exact (pick_sublist s _ t).cons_cons a
  | k + 1, a :: t => by simp only [pick]; exact (pick_sublist s k t).cons a

theorem cuts_sorted {x : List α} (sx : Sorted key x) : (cutsOf key P x).Pairwise (· < ·) := by
  unfold cutsOf
  rw [List.pairwise_map]
  exact sx.sublist (pick_sublist _ _ _)

/-- The pieces of a range cut at rising keys inside it rise. -/
theorem pieces_rise : ∀ (cs : List Key) (r : Range), cs.Pairwise (· < ·) → (∀ c ∈ cs, ¬ c < r.lo) →
    (pieces r cs).Pairwise fun q q' => Range.Above q' q
  | [], _, _, _ => by simp [pieces]
  | c :: cs, r, hs, _ => by
    simp only [pieces]
    obtain ⟨hc, hs'⟩ := List.pairwise_cons.1 hs
    refine List.Pairwise.cons ?_ (pieces_rise cs ⟨c, r.hi⟩ hs' fun c' hc' => Key.lt_asymm (hc c' hc'))
    intro q hq k' k hk' hk
    have hkc : k < c := ((has_iff _ _).1 hk).2 c rfl
    obtain ⟨h1, _⟩ := pieces_ends cs ⟨c, r.hi⟩ q hq
    have hcq : c = q.lo ∨ c < q.lo := by
      rcases h1 with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr (hc _ h1)
    have hlo := ((has_iff _ _).1 hk').1
    rcases Key.not_lt.1 hlo with hlo | hlo
    · rcases hcq with e | e
      · rw [e] at hkc; exact Key.lt_trans hkc hlo
      · exact Key.lt_trans hkc (Key.lt_trans e hlo)
    · rw [hlo]
      rcases hcq with e | e
      · rw [← e]; exact hkc
      · exact Key.lt_trans hkc e

theorem claimRanges_fp (l : List Range) (a : Range → Nat) (b : Range → ByteArray) :
    claimRanges (l.map fun q => Out.claim (.fp q (a q) (b q))) = l := by
  induction l with
  | nil => rfl
  | cons q t ih => simp only [claimRanges, List.map_cons, List.filterMap_cons, Claim.range] at ih ⊢; rw [ih]

/-- A sorted list's items in r, newest first. -/
theorem desc_within {X : List α} (sX : Sorted key X) (r : Range) (p : α → Bool) :
    (((within key r X).filter p).reverse).Pairwise (fun a b => key b < key a) := by
  rw [List.pairwise_reverse]
  exact (sX.filter _).filter _

/-- **An answer is newest first.** From items in key order, an answer's
claims go over its pieces newest first, and every list of ids it sends,
a have or an ids claim, is its items in the claim's range, newest first. -/
theorem answer_newest_first (X : List α) (sX : Sorted key X) (c : Claim) :
    (claimRanges (answer key ident h P X c)).Pairwise Range.Above ∧
    ∀ xs, (Out.hold xs ∈ answer key ident h P X c ∨ ∃ r', Out.claim (.ids r' xs) ∈ answer key ident h P X c) →
      ∃ l : List α, xs = l.map ident ∧ l.Pairwise (fun a b => key b < key a) ∧
        ∀ a ∈ l, a ∈ X ∧ c.range.has (key a) = true := by
  cases c with
  | ids r ys =>
    refine ⟨by simp [answer, claimRanges], fun xs hx => ?_⟩
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      exists_false, Out.hold.injEq] at hx
    subst hx
    refine ⟨((within key r X).filter _).reverse, by rw [List.map_reverse], desc_within sX r _, ?_⟩
    intro a ha
    rw [List.mem_reverse, List.mem_filter] at ha
    exact mem_within.1 ha.1
  | fp r n l =>
    simp only [answer]
    split
    · simp [claimRanges]
    · split
      · refine ⟨by simp [claimRanges], fun xs hx => ?_⟩
        simp only [List.mem_singleton, reduceCtorEq, false_or, Out.claim.injEq, Claim.ids.injEq] at hx
        obtain ⟨_, _, rfl⟩ := hx
        refine ⟨(within key r X).reverse, by rw [List.map_reverse], ?_, ?_⟩
        · rw [List.pairwise_reverse]; exact sX.filter _
        · intro a ha; exact mem_within.1 (List.mem_reverse.1 ha)
      · refine ⟨?_, fun xs hx => ?_⟩
        · rw [claimRanges_fp _ (fun q => (fp key ident h (within key q X)).1)
            (fun q => (fp key ident h (within key q X)).2), List.pairwise_reverse]
          apply pieces_rise _ _ (cuts_sorted (sX.filter _))
          intro c hc
          simp only [cutsOf, List.mem_map] at hc
          obtain ⟨p, hp, rfl⟩ := hc
          exact ((has_iff _ _).1 (mem_within.1 (pick_sub _ _ _ p hp)).2).1
        · rcases hx with hx | ⟨_, hx⟩ <;> simp at hx

end

/-! ## Windows: structure first -/

/-- **A window is the structure range, then claimed times** (from
`max f 1`): each of one class, the structure first. -/
theorem window_first (f : Nat) :
    (window f).Pairwise Range.Before ∧ ∀ q ∈ window f, q.Plain := by
  have hs : ∀ k, (⟨⟨0, 0⟩, some ⟨1, 0⟩⟩ : Range).has k = true → k.t = 0 := by
    intro k hk
    have := ((has_iff _ _).1 hk).2 _ rfl
    simp only [Key.lt_def] at this
    omega
  have ht : ∀ k, (⟨⟨max f 1, 0⟩, none⟩ : Range).has k = true → 1 ≤ k.t := by
    intro k hk
    have := ((has_iff _ _).1 hk).1
    have h1 := Nat.le_max_right f 1
    simp only [Key.lt_def] at this
    omega
  refine ⟨?_, ?_⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) .nil)
    intro q hq k k' hk hk'
    simp only [List.mem_singleton] at hq
    subst hq
    exact Or.inl ⟨hs k hk, by have := ht k' hk'; omega⟩
  · intro q hq
    simp only [window, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · intro k k' hk hk'
      simp [hs k hk, hs k' hk']
    · intro k k' hk hk'
      have := ht k hk
      have := ht k' hk'
      constructor <;> intro <;> omega

/-! ## A message's haves, in order -/

/-- An opening claims the range it opens over. -/
theorem opening_range {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray}
    {P : Params} (Y : List α) (w : Range) : (opening key ident h P Y w).range = w := by
  simp only [opening]; split <;> rfl

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

/-- An answer's haves: its items in the claim's range, newest first. -/
theorem answer_holds (X : List α) (sX : Sorted key X) (c : Claim) :
    ∃ l : List α, (answer key ident h P X c).flatMap holdIds = l.map ident ∧
      l.Pairwise (fun a b => key b < key a) ∧ ∀ a ∈ l, c.range.has (key a) = true := by
  cases c with
  | ids r ys =>
    refine ⟨((within key r X).filter fun a => !ys.any fun i => Decidable.decide (ident a = i)).reverse,
      ?_, desc_within sX r _, ?_⟩
    · simp [answer, holdIds, List.map_reverse]
    · intro a ha
      rw [List.mem_reverse, List.mem_filter] at ha
      exact (mem_within.1 ha.1).2
  | fp r n l =>
    refine ⟨[], ?_, .nil, by simp⟩
    simp only [answer]
    split
    · rfl
    · split
      · simp [holdIds]
      · simp [holdIds, List.flatMap_map]

/-- **Newest first.** Answering claims whose ranges come in sync's order
(structure first, then newest first) and are each of one class, a
message's haves are its items in that order. -/
theorem newest_first (X : List α) (sX : Sorted key X) : ∀ (cs : List Claim),
    (cs.map Claim.range).Pairwise Range.Before → (∀ c ∈ cs, c.range.Plain) →
    ∃ l : List α, (cs.flatMap (answer key ident h P X)).flatMap holdIds = l.map ident ∧
      l.Pairwise (fun a b => first (key a) (key b)) ∧ ∀ a ∈ l, ∃ c ∈ cs, c.range.has (key a) = true
  | [], _, _ => ⟨[], by simp, .nil, by simp⟩
  | c :: cs, hb, hp => by
    obtain ⟨l2, h2, p2, m2⟩ := newest_first X sX cs (List.pairwise_cons.1 hb).2
      (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc'))
    obtain ⟨l1, h1, p1, m1⟩ := answer_holds (key := key) (ident := ident) (h := h) (P := P) X sX c
    refine ⟨l1 ++ l2, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.flatMap_append, h1, h2, List.map_append]
    · rw [List.pairwise_append]
      refine ⟨p1.imp_of_mem fun ha hb' hlt =>
          Or.inr ⟨hp c (List.mem_cons_self ..) _ _ (m1 _ ha) (m1 _ hb'), hlt⟩, p2, ?_⟩
      intro a ha b hb'
      obtain ⟨c', hc', hkb⟩ := m2 b hb'
      exact (List.pairwise_cons.1 hb).1 c'.range (List.mem_map.2 ⟨c', hc', rfl⟩) _ _ (m1 a ha) hkb
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact ⟨c, List.mem_cons_self .., m1 a ha⟩
      · obtain ⟨c', hc', hk⟩ := m2 a ha
        exact ⟨c', List.mem_cons_of_mem _ hc', hk⟩

/-- **A round opens structure first, then newest first**
(`opening_newest_first`): answering the claims a round opens with over a
window (`Conn.start` sends `(window f).map opening`), a side's haves are
its items in sync's order: structure first, then the newest. -/
theorem opening_newest_first (X Y : List α) (sX : Sorted key X) (f : Nat) :
    ∃ l : List α,
      (((window f).map (opening key ident h P Y)).flatMap (answer key ident h P X)).flatMap holdIds =
        l.map ident ∧ l.Pairwise (fun a b => first (key a) (key b)) := by
  obtain ⟨hb, hp⟩ := window_first f
  have hr : ((window f).map (opening key ident h P Y)).map Claim.range = window f := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (window f)]
    exact List.map_congr_left fun w _ => opening_range Y w
  obtain ⟨l, h1, h2, _⟩ := newest_first X sX _ (hr ▸ hb) (by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    rw [opening_range]
    exact hp w hw)
  exact ⟨l, h1, h2⟩

end
end Engine.Sync
