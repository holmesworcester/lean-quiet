/-
The order lists keep, as laws. Bytes compared as memcmp does (`bcmp`)
are compared byte by byte, as lists (`bcmp_eq`, `cmpL`); a position (sort
key, then id) is a strict total order (`Pos.cmp_eq_iff`, `Pos.cmp_swap`,
`Pos.cmp_trans`); a list's rows are sorted (`sortPos_sorted`), so the
first row of a newest-first list is at or after every row filed under
its key (`top_max`). A kind's order laws (its sort key's) rest on these.
-/
import engine.core.Decl

namespace Engine

/-- Byte lists compared as memcmp does: the first differing byte, then
length. -/
def cmpL : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else cmpL xs ys

theorem byte_get (a : ByteArray) (k : Nat) (h : k < a.size) :
    a[k]! = a.data.toList[k]'(by simpa using h) := by
  rw [getElem!_pos a k h]
  rfl

theorem drop_get (a : ByteArray) (k : Nat) (h : k < a.size) :
    a.data.toList.drop k = a[k]! :: a.data.toList.drop (k + 1) := by
  rw [byte_get a k h]
  exact List.drop_eq_getElem_cons _

/-- `bcmp`'s loop from byte k on is the list comparison of the rest. -/
theorem bcmp_loop (a b : ByteArray) : ∀ m k, k + m = min a.size b.size →
    (match (forIn (List.range' k m) ((none : Option Ordering), ())
        (fun i _ => if a[i]! < b[i]! then pure (ForInStep.done (some Ordering.lt, ()))
          else if b[i]! < a[i]! then pure (ForInStep.done (some Ordering.gt, ()))
          else pure (ForInStep.yield (none, ()))) : _root_.Id (Option Ordering × Unit)).run.1 with
     | some r => r | none => compare a.size b.size) =
      cmpL (a.data.toList.drop k) (b.data.toList.drop k) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    simp only [List.range'_zero, List.forIn_nil, Id.run_pure]
    have nil (x : ByteArray) (hx : x.size ≤ k) : x.data.toList.drop k = [] :=
      List.drop_eq_nil_of_le (by simpa using hx)
    have cons (x : ByteArray) (hx : k < x.size) : ∃ y ys, x.data.toList.drop k = y :: ys :=
      List.exists_cons_of_ne_nil fun e => by
        have := congrArg List.length e; simp at this; omega
    rcases Nat.lt_trichotomy a.size b.size with h | h | h
    · obtain ⟨y, ys, e⟩ := cons b (by omega)
      rw [nil a (by omega), e]; simp [cmpL, compare, compareOfLessAndEq, h]
    · rw [nil a (by omega), nil b (by omega)]; simp [cmpL, compare, compareOfLessAndEq, h]
    · obtain ⟨y, ys, e⟩ := cons a (by omega)
      rw [nil b (by omega), e]
      have : ¬ a.size < b.size := by omega
      have : a.size ≠ b.size := by omega
      simp [cmpL, compare, compareOfLessAndEq, *]
  | succ m ih =>
    intro k hk
    rw [drop_get a k (by omega), drop_get b k (by omega), List.range'_succ, List.forIn_cons]
    simp only [cmpL]
    by_cases h1 : a[k]! < b[k]!
    · simp [h1]
    · by_cases h2 : b[k]! < a[k]!
      · simp [h1, h2]
      · simp only [h1, h2, ite_false]
        exact ih (k + 1) (by omega)

/-- **Bytes compare as their lists do.** -/
theorem bcmp_eq (a b : ByteArray) : bcmp a b = cmpL a.data.toList b.data.toList := by
  unfold bcmp
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have := bcmp_loop a b (min a.size b.size) 0 (by omega)
  simp only [List.drop_zero] at this
  rw [← this, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Id.run_bind]
  split <;> rename_i h <;> simp only [h] <;> rfl

/-! ## The list comparison is a total order -/

theorem u8_eq {x y : UInt8} (h1 : ¬ x < y) (h2 : ¬ y < x) : x = y := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2
  exact UInt8.toNat_inj.1 (by omega)

theorem cmpL_swap : ∀ a b : List UInt8, cmpL b a = (cmpL a b).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [cmpL]
    by_cases h1 : x < y
    · have : ¬ y < x := by rw [UInt8.lt_iff_toNat_lt] at *; omega
      simp [h1, this]
    · by_cases h2 : y < x
      · simp [h1, h2]
      · simp only [h1, h2, ite_false]; exact cmpL_swap xs ys

theorem cmpL_eq_iff : ∀ a b : List UInt8, cmpL a b = .eq ↔ a = b
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | x :: xs, y :: ys => by
    simp only [cmpL, List.cons.injEq]
    by_cases h1 : x < y
    · have : x ≠ y := fun e => by subst e; exact absurd h1 (by rw [UInt8.lt_iff_toNat_lt]; omega)
      simp [h1, this]
    · by_cases h2 : y < x
      · have : x ≠ y := fun e => by subst e; exact absurd h2 (by rw [UInt8.lt_iff_toNat_lt]; omega)
        simp [h1, h2, this]
      · obtain rfl := u8_eq h1 h2
        simp only [h1, ite_false, true_and]; exact cmpL_eq_iff xs ys

theorem cmpL_trans : ∀ {a b c : List UInt8}, cmpL a b = .lt → cmpL b c = .lt → cmpL a c = .lt
  | [], [], _, h, _ => by simp [cmpL] at h
  | [], _ :: _, [], _, h => by simp [cmpL] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [cmpL] at h
  | _ :: _, _ :: _, [], _, h => by simp [cmpL] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [cmpL] at *
    by_cases a1 : x < y
    · by_cases b1 : y < z
      · have : x < z := by rw [UInt8.lt_iff_toNat_lt] at *; omega
        simp [this]
      · by_cases b2 : z < y
        · simp [b1, b2] at h2
        · obtain rfl := u8_eq b1 b2; simp [a1]
    · by_cases a2 : y < x
      · simp [a1, a2] at h1
      · obtain rfl := u8_eq a1 a2
        simp only [a1, ite_false] at h1
        by_cases b1 : x < z
        · simp [b1]
        · by_cases b2 : z < x
          · simp [b1, b2] at h2
          · obtain rfl := u8_eq b1 b2
            simp only [b1, ite_false] at h2 ⊢
            exact cmpL_trans h1 h2

theorem cmpL_le_trans {a b c : List UInt8} (h1 : cmpL a b ≠ .gt) (h2 : cmpL b c ≠ .gt) :
    cmpL a c ≠ .gt := by
  have e1 : cmpL a b = .lt ∨ a = b := by
    cases h : cmpL a b
    · exact .inl rfl
    · exact .inr ((cmpL_eq_iff a b).1 h)
    · exact absurd h h1
  have e2 : cmpL b c = .lt ∨ b = c := by
    cases h : cmpL b c
    · exact .inl rfl
    · exact .inr ((cmpL_eq_iff b c).1 h)
    · exact absurd h h2
  rcases e1 with e1 | rfl <;> rcases e2 with e2 | rfl
  · rw [cmpL_trans e1 e2]; simp
  · rw [e1]; simp
  · rw [e2]; simp
  · rw [(cmpL_eq_iff a a).2 rfl]; simp

/-- **Equal-length heads decide first.** -/
theorem cmpL_append : ∀ {a a' : List UInt8} (b b' : List UInt8), a.length = a'.length →
    cmpL (a ++ b) (a' ++ b') = (cmpL a a').then (cmpL b b')
  | [], [], _, _, _ => by simp [cmpL, Ordering.then]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, b, b', h => by
    simp only [List.cons_append, cmpL]
    have h' : xs.length = ys.length := by simpa using h
    split
    · rfl
    · split
      · rfl
      · exact cmpL_append b b' h'

theorem bytes_eq_iff {a b : ByteArray} : a.data.toList = b.data.toList ↔ a = b := by
  constructor
  · intro h
    cases a; cases b
    simp only at h
    rw [Array.toList_inj] at h
    rw [h]
  · rintro rfl; rfl

theorem bcmp_swap (a b : ByteArray) : bcmp b a = (bcmp a b).swap := by
  rw [bcmp_eq, bcmp_eq, cmpL_swap]

theorem bcmp_eq_iff (a b : ByteArray) : bcmp a b = .eq ↔ a = b := by
  rw [bcmp_eq, cmpL_eq_iff, bytes_eq_iff]

/-! ## Positions: a strict total order -/

theorem then_swap (a b : Ordering) : (a.then b).swap = a.swap.then b.swap := by
  cases a <;> rfl

theorem then_eq (a b : Ordering) : a.then b = .eq ↔ a = .eq ∧ b = .eq := by
  cases a <;> simp [Ordering.then]

/-- **Swapping positions swaps their order.** -/
theorem Pos.cmp_swap (p q : Pos) : Pos.cmp q p = (Pos.cmp p q).swap := by
  unfold Pos.cmp
  rw [then_swap, bcmp_swap p.1, bcmp_swap p.2]

/-- **Two positions are level only if they are one**: a position holds
an id, so two rows never tie. -/
theorem Pos.cmp_eq_iff (p q : Pos) : Pos.cmp p q = .eq ↔ p = q := by
  unfold Pos.cmp
  rw [then_eq, bcmp_eq_iff, bcmp_eq_iff]
  exact ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg _ h, congrArg _ h⟩⟩

theorem lt_or_eq_of_ne_gt {a b : ByteArray} (h : bcmp a b ≠ .gt) : bcmp a b = .lt ∨ a = b := by
  cases e : bcmp a b
  · exact .inl rfl
  · exact .inr ((bcmp_eq_iff a b).1 e)
  · exact absurd e h

theorem bcmp_trans {a b c : ByteArray} (h1 : bcmp a b = .lt) (h2 : bcmp b c = .lt) : bcmp a c = .lt := by
  rw [bcmp_eq] at *; exact cmpL_trans h1 h2

/-- **Positions are transitive.** -/
theorem Pos.cmp_trans {p q r : Pos} (h1 : Pos.cmp p q = .lt) (h2 : Pos.cmp q r = .lt) :
    Pos.cmp p r = .lt := by
  unfold Pos.cmp at *
  have k1 : bcmp p.1 q.1 ≠ .gt := fun e => by rw [e] at h1; cases h1
  have k2 : bcmp q.1 r.1 ≠ .gt := fun e => by rw [e] at h2; cases h2
  rcases lt_or_eq_of_ne_gt k1 with e1 | e1 <;> rcases lt_or_eq_of_ne_gt k2 with e2 | e2
  · rw [bcmp_trans e1 e2]; rfl
  · rw [← e2, e1]; rfl
  · rw [e1, e2]; rfl
  · rw [e1, (bcmp_eq_iff _ _).2 rfl] at h1
    rw [e2, (bcmp_eq_iff _ _).2 rfl] at h2
    rw [e1, e2, (bcmp_eq_iff _ _).2 rfl]
    exact bcmp_trans h1 h2

theorem Pos.cmp_le_trans {p q r : Pos} (h1 : Pos.cmp p q ≠ .gt) (h2 : Pos.cmp q r ≠ .gt) :
    Pos.cmp p r ≠ .gt := by
  have e1 : Pos.cmp p q = .lt ∨ p = q := by
    cases h : Pos.cmp p q
    · exact .inl rfl
    · exact .inr ((Pos.cmp_eq_iff p q).1 h)
    · exact absurd h h1
  have e2 : Pos.cmp q r = .lt ∨ q = r := by
    cases h : Pos.cmp q r
    · exact .inl rfl
    · exact .inr ((Pos.cmp_eq_iff q r).1 h)
    · exact absurd h h2
  rcases e1 with e1 | rfl <;> rcases e2 with e2 | rfl
  · rw [Pos.cmp_trans e1 e2]; simp
  · rw [e1]; simp
  · rw [e2]; simp
  · rw [(Pos.cmp_eq_iff p p).2 rfl]; simp

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
      · exact Pos.cmp_le_trans hpq (h.1 z hz)

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
