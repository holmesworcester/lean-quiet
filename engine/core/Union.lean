/-
Several lists read as one: their rows merged in position order and cut
to a limit, their counts summed. A list over a set of keys, "the set-y,
listy way": for example, the messages a device can read are the union of
one list per content key it holds (`Community.readable`).

Each list is read with the same range, order and limit (`View.readAll`),
and the answers merged (`unionAnswers`). A list's first `limit` rows
hold every row the union's first `limit` can need, so merging them and
cutting again gives the union's answer; a reader may rename a list's
rows first if that keeps their order (`Community.readable` names a
receipt's row by its message). The counts are sums, which are right
when the lists are disjoint (a fact filed under one of the keys only).

It is a View like any other: it reads lists, so it runs on SQLite and on
the model, and a notice for any of its keys re-reads it
(`View.view_stable`).

Laws: `eval_readAll` (reading the lists is evaluating each), `mem_union`
(each row is a row of one of the lists), `mem_union_all` (with no limit,
its rows are exactly the lists' rows), and the merge: no read sorts.
Each list comes back in position order (`eval_oriented`; on SQLite, its
index's order), so the union merges them in one pass (`mergeRuns`), and
that merge is exactly the lists' rows sorted (`mergeRuns_eq_sortPos`,
`union_rows`), so a union of lists in order is in order
(`union_sorted`).
-/
import engine.core.View
import engine.core.Decl

namespace Engine
variable {F : Type}

/-! ## Merging lists already in order

Each list comes back in position order (SQLite walks the index it is
filed in; the model's `matching` is sorted, `eval_oriented`), so a union
merges its lists' rows, in one pass, rather than sorting them: no read
sorts. With its lists in order, the merge is exactly `sortPos` of their
rows (`mergeRuns_eq_sortPos`, `union_rows`), so the union is the meaning
it always was. -/

/-- Lists, each in position order, merged into one: the stable merge,
an earlier list's row first on a tie. -/
def mergeRuns {α} (rs : List (List (Pos × α))) : List (Pos × α) :=
  rs.foldr (fun r acc => List.merge r acc posLE) []

/-- A list's rows turned to position order (ascending): reversed if it
was read newest first. -/
def orient {α} (desc : Bool) (l : List α) : List α := if desc then l.reverse else l

/-- The lists' answers as one: their rows merged by position (newest
first if `desc`), cut to `limit`; the counts summed. -/
def unionAnswers (desc : Bool) (limit : Option Nat) (as : List (Answer F)) : Answer F :=
  let ordered := orient desc (mergeRuns (as.map fun a => orient desc a.rows))
  ⟨match limit with | none => ordered | some n => ordered.take n,
    (as.map (·.inRange)).sum, (as.map (·.total)).sum⟩

theorem perm_mergeRuns {α} : ∀ rs : List (List (Pos × α)), (mergeRuns rs).Perm rs.flatten
  | [] => List.Perm.refl _
  | r :: rs => by
    simp only [mergeRuns, List.foldr_cons, List.flatten_cons]
    exact List.Perm.trans (List.merge_perm_append (le := posLE)) (List.Perm.append_left r (perm_mergeRuns rs))

theorem mem_orient {α} {desc : Bool} {l : List α} {a : α} : a ∈ orient desc l ↔ a ∈ l := by
  unfold orient; split <;> simp

/-- x before every row of r: inserting x into r's merge with t is
merging x :: r with t. -/
theorem insertBy_merge {α} (x : Pos × α) (r : List (Pos × α)) (hx : ∀ z ∈ r, posLE x z = true) :
    ∀ t : List (Pos × α), insertBy x (List.merge r t posLE) = List.merge (x :: r) t posLE
  | [] => by
    cases r with
    | nil => simp [insertBy]
    | cons z r' =>
      have := posLE_iff.1 (hx z (List.mem_cons_self ..))
      simp [insertBy, this]
  | y :: t => by
    rw [List.cons_merge_cons]
    by_cases hxy : posLE x y = true
    · rw [ite_eq_left hxy]
      cases r with
      | nil =>
        have := posLE_iff.1 hxy
        simp [insertBy, this]
      | cons z r' =>
        have hz := posLE_iff.1 (hx z (List.mem_cons_self ..))
        have hy := posLE_iff.1 hxy
        rw [List.cons_merge_cons]
        split <;> simp [insertBy, hz, hy]
    · rw [ite_eq_right hxy]
      have hgt : x.1.cmp y.1 = .gt := by simpa [posLE] using hxy
      have hr : List.merge r (y :: t) posLE = y :: List.merge r t posLE := by
        cases r with
        | nil => simp
        | cons z r' =>
          have hzy : posLE z y = false := by
            have := Pos.cmp_gt_of_le (posLE_iff.1 (hx z (List.mem_cons_self ..))) hgt
            simp [posLE, this]
          rw [List.cons_merge_cons, ite_eq_right (by simp [hzy])]
      rw [hr]
      simp only [insertBy, hgt, beq_self_eq_true, ite_true]
      rw [insertBy_merge x r hx t]

/-- Inserting the rows of an ordered list, one at a time, into t is
merging it with t. -/
theorem foldr_insertBy {α} (t : List (Pos × α)) :
    ∀ r : List (Pos × α), r.Pairwise (fun p q => posLE p q = true) → r.foldr insertBy t = List.merge r t posLE
  | [], _ => by simp
  | x :: r, h => by
    rw [List.pairwise_cons] at h
    rw [List.foldr_cons, foldr_insertBy t r h.2, insertBy_merge x r h.1 t]

/-- **Lists in order, merged, are their rows sorted** (`sortPos`). -/
theorem mergeRuns_eq_sortPos {α} :
    ∀ rs : List (List (Pos × α)), (∀ r ∈ rs, r.Pairwise (fun p q => posLE p q = true)) →
      mergeRuns rs = sortPos rs.flatten
  | [], _ => rfl
  | r :: rs, h => by
    show List.merge r (mergeRuns rs) posLE = sortPos (r ++ rs.flatten)
    rw [mergeRuns_eq_sortPos rs (fun r' hr => h r' (List.mem_cons_of_mem _ hr)),
      show sortPos (r ++ rs.flatten) = r.foldr insertBy (sortPos rs.flatten) from List.foldr_append ..,
      foldr_insertBy _ r (h r (List.mem_cons_self ..))]

/-- Read each list. -/
def View.readAll : List ListQ → View F (List (Answer F))
  | [] => pure []
  | q :: qs => do
    let a ← View.read q
    let as ← View.readAll qs
    pure (a :: as)

theorem mem_mergeRuns_orient {desc : Bool} {as : List (Answer F)} {pf : Pos × F} :
    pf ∈ orient desc (mergeRuns (as.map fun a => orient desc a.rows)) ↔ ∃ a ∈ as, pf ∈ a.rows := by
  rw [mem_orient, (perm_mergeRuns _).mem_iff, List.mem_flatten]
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hp⟩
    exact ⟨a, ha, mem_orient.1 hp⟩
  · rintro ⟨a, ha, hp⟩
    exact ⟨_, ⟨a, ha, rfl⟩, mem_orient.2 hp⟩

/-- **Every row of a union is a row of one of its lists.** -/
theorem mem_union {desc : Bool} {limit : Option Nat} {as : List (Answer F)} {pf : Pos × F}
    (h : pf ∈ (unionAnswers desc limit as).rows) : ∃ a ∈ as, pf ∈ a.rows := by
  unfold unionAnswers at h
  apply mem_mergeRuns_orient.1
  cases limit
  · exact h
  · exact List.mem_of_mem_take h

/-- **With no limit, a union holds exactly its lists' rows.** -/
theorem mem_union_all {desc : Bool} {as : List (Answer F)} {pf : Pos × F} :
    pf ∈ (unionAnswers desc none as).rows ↔ ∃ a ∈ as, pf ∈ a.rows := by
  unfold unionAnswers
  exact mem_mergeRuns_orient

/-- **A union of lists in order is their rows sorted**: its rows are
`sortPos` of the lists' rows (each turned to ascending), newest first if
`desc`, cut to `limit`. -/
theorem union_rows {desc : Bool} {limit : Option Nat} {as : List (Answer F)}
    (h : ∀ a ∈ as, (orient desc a.rows).Pairwise (fun p q => posLE p q = true)) :
    (unionAnswers desc limit as).rows =
      let ordered := orient desc (sortPos (as.map fun a => orient desc a.rows).flatten)
      match limit with | none => ordered | some n => ordered.take n := by
  unfold unionAnswers
  rw [mergeRuns_eq_sortPos _ (fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    exact h a ha)]

theorem pairwise_orient_cut {α} {R : α → α → Prop} {desc : Bool} {limit : Option Nat} {l : List α}
    (h : l.Pairwise R) :
    (orient desc (match limit with | none => orient desc l | some n => (orient desc l).take n)).Pairwise R := by
  have hr : l.reverse.Pairwise (fun a b => R b a) := List.pairwise_reverse.2 h
  cases desc <;> cases limit <;> simp only [orient, Bool.false_eq_true, ite_true, ite_false, List.reverse_reverse]
  · exact h
  · exact h.sublist (List.take_sublist _ _)
  · exact h
  · exact List.pairwise_reverse.2 (hr.sublist (List.take_sublist _ _))

/-- **A union of lists in order is in order**: its rows, turned to
ascending, are in position order, cut or not. -/
theorem union_sorted {desc : Bool} {limit : Option Nat} {as : List (Answer F)}
    (h : ∀ a ∈ as, (orient desc a.rows).Pairwise (fun p q => posLE p q = true)) :
    (orient desc (unionAnswers desc limit as).rows).Pairwise (fun p q => posLE p q = true) := by
  rw [union_rows h]
  apply pairwise_orient_cut
  rw [sortPos_eq_fast]
  exact List.pairwise_mergeSort posLE_trans posLE_total _

section
variable [SortKey F]

theorem eval_readAll (s : DB F) (qs : List ListQ) :
    (View.readAll qs : View F _).eval s = qs.map (Engine.eval s) := by
  induction qs with
  | nil => rfl
  | cons q t ih => simp [View.readAll, View.eval_bind, ih]; rfl

/-- What holds pairwise of a list's matches holds of its rows, turned
to ascending: they are a cut of the matches. -/
theorem eval_pairwise {R : Pos × F → Pos × F → Prop} (s : DB F) (q : ListQ)
    (hm : (matching s q).Pairwise R) : (orient q.desc (Engine.eval s q).rows).Pairwise R := by
  have hf := hm.sublist (List.filter_sublist (p := fun p => q.inside p.1))
  unfold Engine.eval orient ListQ.cut
  cases q.desc <;> cases q.limit <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact hf
  · exact hf.sublist (List.take_sublist _ _)
  · simpa [List.pairwise_reverse] using hf
  · have hr : (List.filter (fun p => q.inside p.1) (matching s q)).reverse.Pairwise
        (fun a b => R b a) := List.pairwise_reverse.2 hf
    rw [List.pairwise_reverse]
    exact hr.sublist (List.take_sublist _ _)

/-- **A list's rows are in position order**: ascending, or descending
when it is read newest first. -/
theorem eval_oriented (s : DB F) (q : ListQ) :
    (orient q.desc (Engine.eval s q).rows).Pairwise (fun p r => posLE p r = true) := by
  apply eval_pairwise
  unfold matching
  rw [sortPos_eq_fast]
  exact List.pairwise_mergeSort posLE_trans posLE_total _

/-- **A list's rows are strictly in order**: in a store that keeps the
engine's invariant, no two rows of a list are level (a list names each
op once, `matching_nodup`, and a position holds its op's id). -/
theorem eval_strict {fam : Family F} {s : DB F} (h : Inv fam s) (q : ListQ) :
    (orient q.desc (Engine.eval s q).rows).Pairwise (fun p r => p.1.cmp r.1 = .lt) := by
  have hm : (matching s q).Pairwise (fun p r => posLE p r = true ∧ p.1.2 ≠ r.1.2) := by
    refine List.Pairwise.and ?_ (List.pairwise_map.1 (matching_nodup h q))
    unfold matching
    rw [sortPos_eq_fast]
    exact List.pairwise_mergeSort posLE_trans posLE_total _
  refine (eval_pairwise s q hm).imp fun {p r} ⟨hle, hne⟩ => ?_
  cases e : p.1.cmp r.1
  · rfl
  · exact absurd (congrArg Prod.snd (Pos.cmp_eq e)) hne
  · exact absurd e (posLE_iff.1 hle)

end

end Engine
