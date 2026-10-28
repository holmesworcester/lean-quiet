/-
The engine's tables as plain values, and `Store` over them. The proofs
run the engine here; Engine/Sqlite.lean runs the same code on SQLite,
whose tables these mirror row for row (lists keep SQLite's insertion
order: rowid order, and the queue's seq order).
-/
import engine.core.Core

namespace Engine

structure DB (F : Type) where
  ops : Id → Option Op
  /-- The stored ops' ids, in arrival order: the ops table's rows.
  `ops` alone cannot be walked, and a purge walks them. -/
  stored : List Id
  status : Id → Option (Verdict F)
  waits : Id → List Id
  queue : List Id
  idx : ByteArray → List Id

def DB.empty {F} : DB F := ⟨fun _ => none, [], fun _ => none, fun _ => [], [], fun _ => []⟩

/-- Whether x is in l, by `DecidableEq` (ByteArray's `BEq` has no
`LawfulBEq`). -/
def has (l : List Id) (x : Id) : Bool :=
  match l with
  | [] => false
  | y :: t => if y = x then true else has t x

theorem has_iff (l : List Id) (x : Id) : has l x = true ↔ x ∈ l := by
  induction l with
  | nil => simp [has]
  | cons y t ih =>
    by_cases h : y = x
    · simp [has, h]
    · simp only [has, h, ite_false, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> first | exact absurd rfl h | assumption

/-- A set-like list's insert: appended unless present. -/
def ins (l : List Id) (x : Id) : List Id := if has l x then l else l ++ [x]

theorem mem_ins (l : List Id) (x y : Id) : y ∈ ins l x ↔ y ∈ l ∨ y = x := by
  unfold ins
  by_cases h : has l x = true
  · have := (has_iff l x).1 h
    simp only [h, ite_true]; constructor
    · exact Or.inl
    · rintro (h' | rfl) <;> assumption
  · simp [h]

theorem has_false (l : List Id) (x : Id) : has l x = false ↔ x ∉ l := by
  rw [← has_iff]; simp

/-- Inserting keeps a list's ids distinct. -/
theorem ins_nodup {l : List Id} {x : Id} (h : l.Nodup) : (ins l x).Nodup := by
  unfold ins
  split
  · exact h
  · rename_i hx
    rw [List.nodup_append]
    refine ⟨h, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    intro e; subst e
    exact hx ((has_iff _ _).2 ha)

/-- Ids each once, in byte order: one list for a set, whatever order
its ids were found in. -/
def sortIds (l : List Id) : List Id :=
  (l.foldl ins []).mergeSort fun a b => Decidable.decide (a.toList ≤ b.toList)

theorem mem_sortIds (l : List Id) (x : Id) : x ∈ sortIds l ↔ x ∈ l := by
  have h : ∀ acc : List Id, x ∈ l.foldl ins acc ↔ x ∈ acc ∨ x ∈ l := by
    induction l with
    | nil => simp
    | cons y t ih => intro acc; simp only [List.foldl_cons, ih, mem_ins, List.mem_cons, or_assoc]
  rw [sortIds, List.mem_mergeSort, h]; simp

namespace DB
variable {F : Type}

def putOp (o : Op) (s : DB F) : DB F :=
  { s with ops := fun i => if i = o.id then some o else s.ops i, stored := ins s.stored o.id }
def setStatus (x : Id) (v : Verdict F) (s : DB F) : DB F :=
  { s with status := fun i => if i = x then some v else s.status i }
def addWait (r x : Id) (s : DB F) : DB F :=
  { s with waits := fun i => if i = r then ins (s.waits r) x else s.waits i }
def clearWaiters (r : Id) (s : DB F) : DB F := { s with waits := fun i => if i = r then [] else s.waits i }
def push (x : Id) (s : DB F) : DB F := { s with queue := s.queue ++ [x] }
def index (k : ByteArray) (x : Id) (s : DB F) : DB F :=
  { s with idx := fun i => if i = k then ins (s.idx k) x else s.idx i }

end DB

/-- A state monad written out, so its runs reduce by unfolding. -/
def Model (F : Type) (α : Type) := DB F → α × DB F

instance {F} : Monad (Model F) where
  pure a := fun s => (a, s)
  bind m k := fun s => k (m s).1 (m s).2

def Model.run {F α} (m : Model F α) (s : DB F) : α × DB F := m s

def Model.pop {F} : Model F (Option Id) := fun s =>
  match s.queue with
  | [] => (none, s)
  | x :: q => (some x, { s with queue := q })

instance modelStore {F} : Store F (Model F) where
  getOp x := fun s => (s.ops x, s)
  putOp o := fun s => ((), s.putOp o)
  getStatus x := fun s => (s.status x, s)
  setStatus x v := fun s => ((), s.setStatus x v)
  addWait r x := fun s => ((), s.addWait r x)
  waiters r := fun s => (s.waits r, s)
  clearWaiters r := fun s => ((), s.clearWaiters r)
  push x := fun s => ((), s.push x)
  pop := Model.pop
  index k x := fun s => ((), s.index k x)
  lookup k := fun s => (s.idx k, s)

end Engine
