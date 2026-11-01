/-
A store of two families, read by code written for the first alone.

The node's hooks (app/Commands.lean) read the store as a store of
Community's and Connection's facts. The app's store holds the app's own
ops too (app/Family.lean): a family on top (`Family.sum`). `LeftM B m` is
m read as a store of A: a list keeps its A rows, a verdict its A fact (a
B fact reads as Invalid, as A's validators see one: an A op citing a B
op is Invalid, `Family.sum`), and every other call goes through
unchanged. Code written for A runs on it as written, and hooks written
for A are hooks of the composed store (`Hooks.left`, engine/wire/Node.lean).

Laws: `left_list`. On the model at rest, a list under a key holding only
A's facts answers in `LeftM` exactly as it does on the A part
(`eval_proj`), so a law proven of A's code over the A part speaks of
what that code reads on the composed store (`sum_project`).
`left_status`: a verdict read in `LeftM` is Valid with A's fact f exactly
when the A part's is (`proj_status`).

And the family on top, read in its own lists (`View.liftR`): a key that is
no op's own and none of A's holds only B's facts (`rightKey_of`), and a
B list under one, read newest first, has for its first row a B fact at
or after every one filed under it (`top_right`).
-/
import engine.core.Project
import engine.core.Order

namespace Engine

/-- m, read as a store of A where it holds A and B. -/
def LeftM (_B : Type) (m : Type → Type) (α : Type) : Type := m α

namespace LeftM
variable {A B : Type} {m : Type → Type}

instance [Monad m] : Monad (LeftM B m) := inferInstanceAs (Monad m)

/-- Code written for A, run on the composed store. -/
def run {α : Type} (x : LeftM B m α) : m α := x

/-- A verdict as A's code sees it: a B fact is not one of A's, so A's
validators treat a requirement holding one as Invalid. -/
def verdict : Verdict (A ⊕ B) → Verdict A
  | .valid (.inl a) => .valid a
  | _ => .invalid

/-- An answer's A rows, its counts unchanged (exact under a key holding
only A's facts, `left_list`). -/
def answer (ans : Answer (A ⊕ B)) : Answer A := ⟨ans.lefts, ans.inRange, ans.total⟩

instance [Monad m] [Lists (A ⊕ B) m] : Lists A (LeftM B m) where
  list q := (answer <$> (Lists.list q : m (Answer (A ⊕ B))) : m (Answer A))

instance [Monad m] [Store (A ⊕ B) m] : Store A (LeftM B m) where
  getOp x := (Store.getOp (F := A ⊕ B) x : m _)
  putOp o := (Store.putOp (F := A ⊕ B) o : m _)
  getStatus x := ((·.map verdict) <$> Store.getStatus (F := A ⊕ B) x : m _)
  setStatus x v := (Store.setStatus (F := A ⊕ B) x
    (match v with | .valid a => .valid (.inl a) | .invalid => .invalid) : m _)
  addWait r x := (Store.addWait (F := A ⊕ B) r x : m _)
  waiters r := (Store.waiters (F := A ⊕ B) r : m _)
  clearWaiters r := (Store.clearWaiters (F := A ⊕ B) r : m _)
  push x := (Store.push (F := A ⊕ B) x : m _)
  pop := (Store.pop (F := A ⊕ B) : m _)
  index k x := (Store.index (F := A ⊕ B) k x : m _)
  lookup k := (Store.lookup (F := A ⊕ B) k : m _)
  dependents x := (Store.dependents (F := A ⊕ B) x : m _)
  undecide x := (Store.undecide (F := A ⊕ B) x : m _)
  deleteOp x := (Store.deleteOp (F := A ⊕ B) x : m _)
  countOps := (Store.countOps (F := A ⊕ B) : m _)

instance [Fresh m] : Fresh (LeftM B m) where
  fresh := (Fresh.fresh : m ByteArray)

end LeftM

/-- The B facts of a list, if every one is B's: what a family on top
that cites only its own facts reads. -/
def rights {A B : Type} (fs : List (A ⊕ B)) : Option (List B) :=
  fs.mapM fun | .inr b => some b | .inl _ => none

/-- A view of B's lists, run in a store of A and B: each answer keeps its
B rows (as `View.liftL` keeps A's). -/
def View.liftR {A B α : Type} : View B α → View (A ⊕ B) α
  | .pure a => .pure a
  | .list q k => .list q fun ans => (k ⟨ans.rights, ans.inRange, ans.total⟩).liftR

section
variable {A B : Type} [SortKey A] [SortKey B] {a : Family A} {b : Family₂ A B} {s : DB (A ⊕ B)}

/-- **`left_list`: A's code reads the composed store as the A part.** At
rest, a list under a key holding only A's facts answers in `LeftM` what
it answers on the A part, and changes nothing. -/
theorem left_list (h : Inv (a.sum b) s) (hq : s.queue = []) {q : ListQ} (hk : LeftKey s q.key) :
    Model.run (Lists.list q : LeftM B (Model (A ⊕ B)) (Answer A)) s = (eval (s.proj a b.owns) q, s) := by
  show (LeftM.answer (eval s q), s) = _
  rw [eval_proj h hq hk]
  simp only [LeftM.answer, Answer.lefts]
  rw [filterMap_inlRow (fun _ => rfl)]

omit [SortKey A] [SortKey B] in
/-- **`left_status`: A's code sees a Valid A verdict exactly where the A
part has it,** at rest, and changes nothing. -/
theorem left_status (h : Inv (a.sum b) s) (hq : s.queue = []) (x : Id) (f : A) :
    (Model.run (Store.getStatus (F := A) x : LeftM B (Model (A ⊕ B)) _) s).1 = some (.valid f) ↔
      (s.proj a b.owns).status x = some (.valid f) := by
  rw [proj_status h hq]
  show (s.status x).map LeftM.verdict = _ ↔ _
  cases hs : s.status x with
  | none => simp
  | some v =>
    cases v with
    | invalid => simp [LeftM.verdict]
    | valid g => cases g <;> simp [LeftM.verdict]

end

/-! ## The family on top -/

section
variable {A B : Type} {a : Family A} {b : Family₂ A B}

/-- Keys under which a store of A and B files only B's facts. -/
def RightKey (s : DB (A ⊕ B)) (k : ByteArray) : Prop :=
  ∀ x ∈ s.idx k, ∃ g, s.status x = some (.valid (.inr g))

/-- **A key that is no op's own key and none of A's keys holds only B's
facts.** -/
theorem rightKey_of {s : DB (A ⊕ B)} (h : Inv (a.sum b) s) {k : ByteArray}
    (hop : ∀ y, k ≠ opKey y) (ha : ∀ f, k ∉ a.keys f) : RightKey s k := by
  intro x hx
  obtain ⟨f, hf, hk⟩ := (h.idx k x).1 hx
  cases f with
  | inr g => exact ⟨g, hf⟩
  | inl f =>
    rcases List.mem_cons.1 hk with e | e
    · exact absurd e (hop x)
    · exact absurd e (ha f)

/-- **The first row of a newest-first list under a key holding only B's
facts is a B fact, at or after every one filed under it.** -/
theorem top_right [SortKey A] [SortKey B] {s : DB (A ⊕ B)} {k : ByteArray} {lim : Option Nat}
    (hk : RightKey s k) (hl : lim ≠ some 0) {x : Id} {g : B} (hx : x ∈ s.idx k)
    (hg : s.status x = some (.valid (.inr g))) :
    ∃ y g', (eval s { key := k, limit := lim }).rows.head? = some ((SortKey.sortOf g', y), .inr g') ∧
      s.status y = some (.valid (.inr g')) ∧ Pos.cmp (SortKey.sortOf g, x) (SortKey.sortOf g', y) ≠ .gt := by
  have hm : ((SortKey.sortOf (Sum.inr g : A ⊕ B), x), (Sum.inr g : A ⊕ B)) ∈ matching s { key := k, limit := lim } :=
    (mem_matching k lim).2 ⟨x, _, rfl, hx, hg⟩
  obtain ⟨t, ht, htm, hle⟩ := top_max rfl rfl rfl hl hm
  obtain ⟨y, f, rfl, hy, hf⟩ := (mem_matching k lim).1 htm
  obtain ⟨g', hg'⟩ := hk y hy
  rw [hf] at hg'
  cases hg'
  exact ⟨y, g', ht, hf, hle⟩

/-- A view of B, run lifted on the store, reads each list's B rows. -/
theorem eval_liftR_list {s : DB (A ⊕ B)} {α : Type} [SortKey A] [SortKey B] (q : ListQ)
    (k : Answer B → View B α) :
    ((View.list q k).liftR : View (A ⊕ B) α).eval s =
      ((k ⟨(eval s q).rights, (eval s q).inRange, (eval s q).total⟩).liftR).eval s := rfl

end
end Engine
