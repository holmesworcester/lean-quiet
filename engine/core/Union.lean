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
(each row is a row of one of the lists), and `mem_union_all` (with no
limit, its rows are exactly the lists' rows).
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

section
variable [SortKey F]

theorem eval_readAll (s : DB F) (qs : List ListQ) :
    (View.readAll qs : View F _).eval s = qs.map (Engine.eval s) := by
  induction qs with
  | nil => rfl
  | cons q t ih => simp [View.readAll, View.eval_bind, ih]; rfl

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
