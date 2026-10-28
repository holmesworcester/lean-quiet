/-
Views: what a screen or the network reads, as a composition of lists in
which a later list may depend on earlier answers. A view is a value, so
the lists it reads, and the keys to watch, are explicit in it; nothing
is recorded. It runs where lists are read: on SQLite (what runs) or on
the model (its meaning).

The law: a list's answer changes only if a row is filed under its key
(`eval_stable`); so a view's answer changes only if a row is filed under
one of the keys it read (`view_stable`). A notice for exactly those keys
is all a live view needs: notices are complete.
-/
import Engine.Query
import Engine.Proofs

namespace Engine

inductive View (F α : Type) where
  | pure (a : α)
  | list (q : ListQ) (k : Answer F → View F α)

namespace View
variable {F α β : Type}

def bind : View F α → (α → View F β) → View F β
  | pure a, f => f a
  | list q k, f => list q fun a => bind (k a) f

instance : Monad (View F) where
  pure := View.pure
  bind := View.bind

/-- Read one list. -/
def read (q : ListQ) : View F (Answer F) := list q View.pure

/-- Run a view where lists are read. -/
def run {m : Type → Type} [Monad m] [Lists F m] : View F α → m α
  | pure a => Pure.pure a
  | list q k => do run (k (← Lists.list q))

section
variable [SortKey F]

/-- A view's answer over the model's tables. -/
def eval (s : DB F) : View F α → α
  | pure a => a
  | list q k => eval s (k (Engine.eval s q))

/-- The keys of the lists a view reads over these tables: what to watch. -/
def keys (s : DB F) : View F α → List ByteArray
  | pure _ => []
  | list q k => q.key :: keys s (k (Engine.eval s q))

/-- On the model, running a view is evaluating it. -/
theorem run_model (v : View F α) (s : DB F) : (v.run : Model F α).run s = (v.eval s, s) := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval s q)

@[simp] theorem eval_pure (s : DB F) (a : α) : (Pure.pure a : View F α).eval s = a := rfl

@[simp] theorem eval_bind (s : DB F) (v : View F α) (f : α → View F β) :
    (v >>= f).eval s = (f (v.eval s)).eval s := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval s q)

theorem eval_bind' (s : DB F) (v : View F α) (f : α → View F β) :
    (v.bind f).eval s = (f (v.eval s)).eval s := eval_bind s v f

@[simp] theorem eval_read (s : DB F) (q : ListQ) : (read q : View F (Answer F)).eval s = Engine.eval s q :=
  rfl

end
end View

/-! ## Stability -/

section
variable {F : Type} {fam : Family F}

/-- Tables t come after s: t is reached from s by ingesting and judging. -/
inductive Later (fam : Family F) : DB F → DB F → Prop
  | refl (s : DB F) : Later fam s s
  | ingest {s t : DB F} (o : Op) : Later fam s t → Later fam s (ingestS o t)
  | step {s t : DB F} : Later fam s t → Later fam s (stepS fam t)

theorem ingestS_status (o : Op) (s : DB F) : (ingestS o s).status = s.status := by
  unfold ingestS; split <;> rfl

/-- A step decides at most the op it judges, and only if it was
undecided: verdicts already made stay. -/
theorem stepS_keeps {s : DB F} {x : Id} {v : Verdict F} (h : s.status x = some v) :
    (stepS fam s).status x = some v := by
  unfold stepS
  cases hq : s.queue with
  | nil => exact h
  | cons y q =>
    simp only
    cases hy : s.status y with
    | some _ => exact h
    | none =>
      simp only
      cases s.ops y with
      | none => exact h
      | some o =>
        simp only
        cases judge fam o (o.reqs.map s.status) with
        | some w =>
          rw [(decideS_fields (fam := fam) y w _).2.1]
          have : x ≠ y := fun e => by rw [e, hy] at h; cases h
          simp only [this, ite_false]; exact h
        | none => rw [waitOnS_status]; exact h

theorem later_keeps {s t : DB F} (h : Later fam s t) {x : Id} {v : Verdict F}
    (hx : s.status x = some v) : t.status x = some v := by
  induction h with
  | refl => exact hx
  | ingest o _ ih => rw [ingestS_status]; exact ih
  | step _ ih => exact stepS_keeps ih

theorem later_inv {s t : DB F} (h : Later fam s t) (hs : Inv fam s) : Inv fam t := by
  induction h with
  | refl => exact hs
  | ingest o _ ih => exact inv_ingest ih o
  | step _ ih => exact inv_step ih

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)]

variable [SortKey F]

/-- **A list changes only if a row is filed under its key.** If no row
was filed under q's key between s and t, q answers the same: its rows,
their facts, order and counts. Its other conjuncts need no watching: a
fact's keys are all filed when it is decided, and verdicts are final. -/
theorem eval_stable {s t : DB F} (hs : Inv fam s) (h : Later fam s t) {q : ListQ}
    (hk : t.idx q.key = s.idx q.key) : eval t q = eval s q := by
  have ht := later_inv h hs
  have hst : ∀ x v, s.status x = some v → t.status x = some v := fun _ _ => later_keeps h
  have hm : matching t q = matching s q := by
    unfold matching
    rw [hk]
    congr 1
    refine filterMap_congr' fun x hx => ?_
    obtain ⟨f, hf, _⟩ := (hs.idx q.key x).1 hx
    have htf := hst x _ hf
    have hhas : ∀ k, has (t.idx k) x = has (s.idx k) x := by
      intro k
      have e : x ∈ t.idx k ↔ x ∈ s.idx k := by
        rw [ht.idx, hs.idx]
        constructor
        · rintro ⟨g, hg, hk'⟩; rw [htf] at hg; cases hg; exact ⟨f, hf, hk'⟩
        · rintro ⟨g, hg, hk'⟩; rw [hf] at hg; cases hg; exact ⟨f, htf, hk'⟩
      exact Bool.eq_iff_iff.2 ((has_iff _ x).trans (e.trans (has_iff _ x).symm))
    simp only [hhas, htf, hf]
  unfold eval; rw [hm]

/-- **A view changes only if a row is filed under a key it read.** -/
theorem view_stable {α : Type} {s t : DB F} (hs : Inv fam s) (h : Later fam s t) (v : View F α)
    (hk : ∀ k ∈ v.keys s, t.idx k = s.idx k) : v.eval t = v.eval s := by
  induction v with
  | pure a => rfl
  | list q k ih =>
    have hq : eval t q = eval s q := eval_stable hs h (hk q.key (List.mem_cons_self ..))
    show View.eval t (k (eval t q)) = View.eval s (k (eval s q))
    rw [hq]
    exact ih (eval s q) fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')

end

end Engine
