/-
The order lists keep, as laws, past what `Engine.Query` proves for the
sort that runs (`bcmp_eq_lexCmp`, `bcmp_eq`, `Pos.cmp_swap`,
`Pos.cmp_trans`): a position is a strict total order (`Pos.cmp_eq_iff`,
`Pos.cmp_lt_trans`); equal-length heads decide first (`lexCmp_append`);
a list's rows are sorted (`sortPos_sorted`), so the first row of a
newest-first list is at or after every row filed under its key
(`top_max`). A kind's order laws (its sort key's) rest on these.
-/
import engine.core.Decl

namespace Engine

theorem lexCmp_self : ∀ xs : List UInt8, lexCmp xs xs = .eq
  | [] => rfl
  | x :: xs => by
    have : ¬ x < x := by rw [UInt8.lt_iff_toNat_lt]; omega
    simp only [lexCmp, this, ite_false]
    exact lexCmp_self xs

/-- **Equal-length heads decide first.** -/
theorem lexCmp_append : ∀ {a a' : List UInt8} (b b' : List UInt8), a.length = a'.length →
    lexCmp (a ++ b) (a' ++ b') = (lexCmp a a').then (lexCmp b b')
  | [], [], _, _, _ => by simp [lexCmp, Ordering.then]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, b, b', h => by
    simp only [List.cons_append, lexCmp]
    have h' : xs.length = ys.length := by simpa using h
    split
    · rfl
    · split
      · rfl
      · exact lexCmp_append b b' h'

theorem bcmp_eq_iff (a b : ByteArray) : bcmp a b = .eq ↔ a = b :=
  ⟨bcmp_eq, fun h => by rw [h, bcmp_eq_lexCmp, lexCmp_self]⟩

theorem then_eq (a b : Ordering) : a.then b = .eq ↔ a = .eq ∧ b = .eq := by
  cases a <;> simp [Ordering.then]

/-! ## Positions: a strict total order -/

/-- **Two positions are level only if they are one**: a position holds
an id, so two rows never tie. -/
theorem Pos.cmp_eq_iff (p q : Pos) : Pos.cmp p q = .eq ↔ p = q := by
  unfold Pos.cmp
  rw [then_eq, bcmp_eq_iff, bcmp_eq_iff]
  exact ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg _ h, congrArg _ h⟩⟩

theorem strict_of {p q : Pos} (h : Pos.cmp p q ≠ .gt) (hne : p ≠ q) : Pos.cmp p q = .lt := by
  cases e : Pos.cmp p q
  · rfl
  · exact absurd ((Pos.cmp_eq_iff p q).1 e) hne
  · exact absurd e h

/-- **Sorting before is transitive.** -/
theorem Pos.cmp_lt_trans {p q r : Pos} (h1 : Pos.cmp p q = .lt) (h2 : Pos.cmp q r = .lt) :
    Pos.cmp p r = .lt := by
  refine strict_of (Pos.cmp_trans (by rw [h1]; decide) (by rw [h2]; decide)) fun e => ?_
  subst e
  have := Pos.cmp_swap p q
  rw [h1, h2] at this
  cases this

/-! ## Nothing lies between a position and its id followed by a zero -/

/-- xs sorts before ys ++ [0] exactly when it is not past ys. -/
theorem lexCmp_append_zero : ∀ xs ys : List UInt8, lexCmp xs (ys ++ [0]) = .lt ↔ lexCmp xs ys ≠ .gt
  | [], [] => by simp [lexCmp]
  | [], _ :: _ => by simp [lexCmp]
  | x :: xs, [] => by
    have : ¬ x < 0 := by simp [UInt8.lt_iff_toNat_lt]
    simp only [List.nil_append, lexCmp, this, ite_false]
    constructor
    · intro h
      split at h
      · cases h
      · cases xs <;> simp [lexCmp] at h
    · intro h; exact absurd rfl h
  | x :: xs, y :: ys => by
    simp only [List.cons_append, lexCmp]
    split
    · simp
    · split
      · simp
      · exact lexCmp_append_zero xs ys

theorem bcmp_push_zero (a b : ByteArray) : bcmp a (b.push 0) = .lt ↔ bcmp a b ≠ .gt := by
  rw [bcmp_eq_lexCmp, bcmp_eq_lexCmp, ByteArray.data_push, Array.toList_push]
  exact lexCmp_append_zero _ _

/-- **A position's successor**: (p.1, p.2 ++ [0]) is the least position
past p, so "before it" is "at or before p" (a window's older side). -/
theorem Pos.cmp_succ (r p : Pos) : Pos.cmp r (p.1, p.2.push 0) = .lt ↔ Pos.cmp r p ≠ .gt := by
  unfold Pos.cmp
  cases h : bcmp r.1 p.1
  · simp [Ordering.then]
  · simp only [Ordering.then]
    exact bcmp_push_zero _ _
  · simp [Ordering.then]

/-- **A list's range and its complement partition it**: of one key's
uncapped list, the rows past a and the rows before a's successor (at or
before a) are all of its rows, each once. -/
theorem eval_partition [SortKey F] (s : DB F) {q₁ q₂ : ListQ} (a : Pos) (hk : q₂.key = q₁.key)
    (ha : q₂.also = q₁.also) (h1 : q₁.after = some a) (h1' : q₁.before = none) (h2 : q₂.after = none)
    (h2' : q₂.before = some (a.1, a.2.push 0)) (c1 : q₁.cap = 0) (c2 : q₂.cap = 0) :
    (eval s q₁).inRange + (eval s q₂).inRange = (eval s q₁).total := by
  have hm : matching s q₂ = matching s q₁ := by unfold matching; rw [hk, ha]
  simp only [eval, capped, c1, c2, ite_true, hm]
  have hc : ∀ r : Pos × F, q₂.inside r.1 = !q₁.inside r.1 := fun r => by
    simp only [ListQ.inside, h1, h1', h2, h2', Bool.and_true, Bool.true_and]
    cases e : Pos.cmp r.1 a
    · have := (Pos.cmp_succ r.1 a).2 (by rw [e]; decide); simp [this]
    · have := (Pos.cmp_succ r.1 a).2 (by rw [e]; decide); simp [this]
    · have : Pos.cmp r.1 (a.1, a.2.push 0) ≠ .lt := fun h => absurd ((Pos.cmp_succ r.1 a).1 h) (by rw [e]; decide)
      cases e' : Pos.cmp r.1 (a.1, a.2.push 0) <;> simp_all
  generalize matching s q₁ = l
  induction l with
  | nil => rfl
  | cons r t ih =>
    have h2r := hc r
    cases h : q₁.inside r.1 <;> rw [h] at h2r <;>
      simp only [List.filter_cons, h, h2r, Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true, List.length_cons] <;> omega

/-! ## Lists are sorted -/

/-- Rows in position order, ascending. -/
def Sorted {α} (l : List (Pos × α)) : Prop := l.Pairwise fun a b => Pos.cmp a.1 b.1 ≠ .gt

theorem insertBy_sorted {α} (p : Pos × α) : ∀ {l : List (Pos × α)}, Sorted l → Sorted (insertBy p l)
  | [], _ => List.pairwise_singleton _ _
  | q :: t, h => by
    unfold insertBy
    rw [Sorted, List.pairwise_cons] at h
    split
    · rename_i hgt
      have hqp : Pos.cmp q.1 p.1 ≠ .gt := by
        rw [Pos.cmp_swap]; simp only [beq_iff_eq] at hgt; rw [hgt]; simp [Ordering.swap]
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, insertBy_sorted p h.2⟩
      rcases List.mem_cons.1 ((perm_insertBy p t).mem_iff.1 hz) with rfl | hz
      · exact hqp
      · exact h.1 z hz
    · rename_i hgt
      have hpq : Pos.cmp p.1 q.1 ≠ .gt := by simpa using hgt
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, List.pairwise_cons.2 h⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hpq
      · exact Pos.cmp_trans hpq (h.1 z hz)

/-- **A list's rows are in position order.** -/
theorem sortPos_sorted {α} : ∀ l : List (Pos × α), Sorted (sortPos l)
  | [] => List.Pairwise.nil
  | p :: t => insertBy_sorted p (sortPos_sorted t)

theorem sorted_last {α} : ∀ {l : List (Pos × α)} {t : Pos × α}, Sorted l → l.getLast? = some t →
    ∀ p ∈ l, Pos.cmp p.1 t.1 ≠ .gt
  | [], _, _, h, _, hp => by simp at h
  | [a], t, _, h, p, hp => by
    simp at h hp; subst h; subst hp; rw [(Pos.cmp_eq_iff _ _).2 rfl]; simp
  | a :: b :: rest, t, hs, h, p, hp => by
    rw [Sorted, List.pairwise_cons] at hs
    have h' : (b :: rest).getLast? = some t := by simpa [List.getLast?_cons_cons] using h
    have ht : t ∈ b :: rest := List.mem_of_getLast? h'
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hs.1 t ht
    · exact sorted_last hs.2 h' p hp

/-- **The first row of a newest-first list is the newest.** Read with no
range and a limit other than 0, a list whose key holds row p has a first
row, at or after p. -/
theorem top_max [SortKey F] {s : DB F} {q : ListQ} (ha : q.after = none) (hb : q.before = none)
    (hd : q.desc = true) (hl : q.limit ≠ some 0) {p : Pos × F} (hp : p ∈ matching s q) :
    ∃ t, (eval s q).rows.head? = some t ∧ t ∈ matching s q ∧ Pos.cmp p.1 t.1 ≠ .gt := by
  have hin : (matching s q).filter (fun r => q.inside r.1) = matching s q := by
    apply List.filter_eq_self.2
    intro r _; simp [ListQ.inside, ha, hb]
  have hne : matching s q ≠ [] := List.ne_nil_of_mem hp
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
  refine ⟨t, ?_, List.mem_of_getLast? ht, sorted_last (sortPos_sorted _) ht p hp⟩
  unfold eval
  simp only [hin, hd, ite_true, ListQ.cut]
  have hr : (matching s q).reverse.head? = some t := by rw [List.head?_reverse, ht]
  split
  · exact hr
  · rename_i n hn
    cases n with
    | zero => exact absurd hn hl
    | succ n => rw [List.head?_take]; simp [hr]

end Engine
