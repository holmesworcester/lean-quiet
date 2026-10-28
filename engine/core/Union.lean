/-
Several lists read as one: their rows merged in position order and cut
to a limit, their counts summed. A list over a set of keys, "the set-y,
listy way": for example, the messages a device can read are the union of
one list per content key it holds (`Community.readable`).

Each list is read with the same range, order and limit. Its first
`limit` rows hold every row the union's first `limit` can need, so
merging them and cutting again gives the union's answer. The counts are
sums, which are right when the lists are disjoint (a fact filed under
one of the keys only).

It is a View like any other: it reads lists, so it runs on SQLite and on
the model, and a notice for any of its keys re-reads it
(`View.view_stable`).

Laws: `eval_union` (its answer is the merge of the lists' answers),
`mem_union` (each row is a row of one of the lists), and `mem_union_all`
(with no limit, its rows are exactly the lists' rows).
-/
import engine.core.View
import engine.core.Decl

namespace Engine
variable {F : Type}

/-- The lists' answers as one: rows merged by position (newest first if
`desc`), cut to `limit`; the counts summed. -/
def unionAnswers (desc : Bool) (limit : Option Nat) (as : List (Answer F)) : Answer F :=
  let merged := sortPos (as.flatMap (·.rows))
  let ordered := if desc then merged.reverse else merged
  ⟨match limit with | none => ordered | some n => ordered.take n,
    (as.map (·.inRange)).sum, (as.map (·.total)).sum⟩

/-- Read each list. -/
def View.readAll : List ListQ → View F (List (Answer F))
  | [] => pure []
  | q :: qs => do
    let a ← View.read q
    let as ← View.readAll qs
    pure (a :: as)

/-- Several lists read as one, each with the given limit and order. -/
def View.union (qs : List ListQ) (limit : Option Nat) (desc : Bool := true) : View F (Answer F) := do
  let as ← View.readAll (qs.map fun q => { q with limit, desc })
  pure (unionAnswers desc limit as)

section
variable [SortKey F]

theorem eval_readAll (s : DB F) (qs : List ListQ) :
    (View.readAll qs : View F _).eval s = qs.map (Engine.eval s) := by
  induction qs with
  | nil => rfl
  | cons q t ih => simp [View.readAll, View.eval_bind, ih]; rfl

/-- **A union's answer is the merge of its lists' answers.** -/
theorem eval_union (s : DB F) (qs : List ListQ) (limit : Option Nat) (desc : Bool) :
    (View.union qs limit desc : View F _).eval s =
      unionAnswers desc limit (qs.map fun q => Engine.eval s { q with limit, desc }) := by
  simp [View.union, View.eval_bind, eval_readAll, List.map_map]
  rfl

/-- **Every row of a union is a row of one of its lists.** -/
theorem mem_union {desc : Bool} {limit : Option Nat} {as : List (Answer F)} {pf : Pos × F}
    (h : pf ∈ (unionAnswers desc limit as).rows) : ∃ a ∈ as, pf ∈ a.rows := by
  unfold unionAnswers at h
  have h' : pf ∈ sortPos (as.flatMap (·.rows)) := by
    cases limit <;> cases desc <;> simp only [ite_true, Bool.false_eq_true, ite_false] at h
    · exact h
    · exact List.mem_reverse.1 h
    · exact List.mem_of_mem_take h
    · exact List.mem_reverse.1 (List.mem_of_mem_take h)
  rw [mem_sortPos, List.mem_flatMap] at h'
  exact h'

/-- **With no limit, a union holds exactly its lists' rows.** -/
theorem mem_union_all {desc : Bool} {as : List (Answer F)} {pf : Pos × F} :
    pf ∈ (unionAnswers desc none as).rows ↔ ∃ a ∈ as, pf ∈ a.rows := by
  unfold unionAnswers
  cases desc <;> simp [mem_sortPos, List.mem_flatMap]

end

end Engine
