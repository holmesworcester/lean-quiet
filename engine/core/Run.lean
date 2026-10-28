/-
The engine's code run on the model, as plain functions of the tables:
each lemma says what one routine does to a `DB`.
-/
import Engine.Model

namespace Engine
variable {F : Type}

@[simp] theorem Model.run_bind {α β} (m : Model F α) (k : α → Model F β) (s : DB F) :
    (m >>= k).run s = (k (m.run s).1).run (m.run s).2 := rfl
@[simp] theorem Model.run_pure {α} (a : α) (s : DB F) : (pure a : Model F α).run s = (a, s) := rfl

@[simp] theorem run_getOp (x : Id) (s : DB F) :
    (Store.getOp x : Model F _).run s = (s.ops x, s) := rfl
@[simp] theorem run_putOp (o : Op) (s : DB F) :
    (Store.putOp o : Model F _).run s = ((), s.putOp o) := rfl
@[simp] theorem run_getStatus (x : Id) (s : DB F) :
    (Store.getStatus x : Model F _).run s = (s.status x, s) := rfl
@[simp] theorem run_setStatus (x : Id) (v : Verdict F) (s : DB F) :
    (Store.setStatus x v : Model F _).run s = ((), s.setStatus x v) := rfl
@[simp] theorem run_addWait (r x : Id) (s : DB F) :
    (Store.addWait r x : Model F _).run s = ((), s.addWait r x) := rfl
@[simp] theorem run_waiters (r : Id) (s : DB F) :
    (Store.waiters r : Model F _).run s = (s.waits r, s) := rfl
@[simp] theorem run_clearWaiters (r : Id) (s : DB F) :
    (Store.clearWaiters r : Model F _).run s = ((), s.clearWaiters r) := rfl
@[simp] theorem run_push (x : Id) (s : DB F) :
    (Store.push x : Model F _).run s = ((), s.push x) := rfl
@[simp] theorem run_index (k : ByteArray) (x : Id) (s : DB F) :
    (Store.index k x : Model F _).run s = ((), s.index k x) := rfl
@[simp] theorem run_lookup (k : ByteArray) (s : DB F) :
    (Store.lookup k : Model F _).run s = (s.idx k, s) := rfl
theorem run_pop_nil (s : DB F) (h : s.queue = []) :
    (Store.pop : Model F _).run s = (none, s) := by
  show Model.pop s = _; unfold Model.pop; rw [h]
theorem run_pop_cons (s : DB F) (x : Id) (q : List Id) (h : s.queue = x :: q) :
    (Store.pop : Model F _).run s = (some x, { s with queue := q }) := by
  show Model.pop s = _; unfold Model.pop; rw [h]

theorem run_statuses (l : List Id) (s : DB F) :
    (statuses l : Model F _).run s = (l.map s.status, s) := by
  induction l with
  | nil => rfl
  | cons r t ih =>
    simp only [statuses, Model.run_bind, run_getStatus, ih]; rfl

def waitOnS (x : Id) : List Id → DB F → DB F
  | [], s => s
  | r :: t, s => waitOnS x t (if (s.status r).isNone then s.addWait r x else s)

theorem run_waitOn (x : Id) (l : List Id) (s : DB F) :
    (waitOn (F := F) x l : Model F _).run s = ((), waitOnS x l s) := by
  induction l generalizing s with
  | nil => rfl
  | cons r t ih =>
    simp only [waitOn, waitOnS, Model.run_bind, run_getStatus]
    by_cases h : (s.status r).isNone = true
    · simp [h, ih]
    · simp [h, ih]

def pushAllS (ws : List Id) (s : DB F) : DB F := { s with queue := s.queue ++ ws }

theorem run_pushAll (ws : List Id) (s : DB F) :
    (pushAll (F := F) ws : Model F _).run s = ((), pushAllS ws s) := by
  induction ws generalizing s with
  | nil => simp [pushAll, pushAllS]
  | cons w t ih =>
    simp only [pushAll, Model.run_bind, run_push, ih]
    simp [pushAllS, DB.push]

def indexAllS (x : Id) : List ByteArray → DB F → DB F
  | [], s => s
  | k :: t, s => indexAllS x t (s.index k x)

theorem run_indexAll (x : Id) (ks : List ByteArray) (s : DB F) :
    (indexAll (F := F) x ks : Model F _).run s = ((), indexAllS x ks s) := by
  induction ks generalizing s with
  | nil => rfl
  | cons k t ih => simp only [indexAll, indexAllS, Model.run_bind, run_index, ih]

def decideS (fam : Family F) (x : Id) (v : Verdict F) (s : DB F) : DB F :=
  let s1 := s.setStatus x v
  let s2 := match v with
    | .valid f => indexAllS x (fam.fileKeys x f) s1
    | .invalid => s1
  pushAllS (s2.waits x) (s2.clearWaiters x)

theorem run_decide (fam : Family F) (x : Id) (v : Verdict F) (s : DB F) :
    (decide (m := Model F) fam x v).run s = ((), decideS fam x v s) := by
  cases v with
  | valid f =>
    simp only [decide, Model.run_bind, run_setStatus, run_indexAll, run_waiters,
      run_clearWaiters, run_pushAll]; rfl
  | invalid =>
    simp only [decide, Model.run_bind, run_setStatus, run_waiters,
      run_clearWaiters, run_pushAll]; rfl

def ingestS (o : Op) (s : DB F) : DB F :=
  match s.ops o.id with
  | some _ => s
  | none => (s.putOp o).push o.id

theorem run_ingest (o : Op) (s : DB F) :
    (ingest (m := Model F) o).run s = ((), ingestS o s) := by
  unfold ingest ingestS
  cases h : s.ops o.id with
  | some _ => simp only [Model.run_bind, run_getOp, h]; rfl
  | none => simp only [Model.run_bind, run_getOp, h, run_putOp, run_push]

/-- One step on the model: the op at the queue's head, judged. -/
def stepS (fam : Family F) (s : DB F) : DB F :=
  match s.queue with
  | [] => s
  | x :: q =>
    let s1 := { s with queue := q }
    match s1.status x with
    | some _ => s1
    | none => match s1.ops x with
      | none => s1
      | some o => match judge fam o (o.reqs.map s1.status) with
        | some v => decideS fam x v s1
        | none => waitOnS x o.reqs s1

theorem run_step (fam : Family F) (s : DB F) :
    (step (m := Model F) fam).run s = (!s.queue.isEmpty, stepS fam s) := by
  unfold step stepS
  cases hq : s.queue with
  | nil => simp only [Model.run_bind, run_pop_nil s hq]; rfl
  | cons x q =>
    simp only [Model.run_bind, run_pop_cons s x q hq, run_getStatus]
    cases hs : s.status x with
    | some _ => rfl
    | none =>
      simp only [Model.run_bind, run_getOp]
      cases ho : s.ops x with
      | none => rfl
      | some o =>
        simp only [Model.run_bind, run_statuses]
        cases hj : judge fam o (o.reqs.map s.status) with
        | some v => simp only [Model.run_bind, run_decide]; rfl
        | none => simp only [Model.run_bind, run_waitOn]; rfl

def drainS (fam : Family F) : Nat → DB F → DB F
  | 0, s => s
  | n + 1, s => if s.queue.isEmpty then stepS fam s else drainS fam n (stepS fam s)

theorem run_drain (fam : Family F) (n : Nat) (s : DB F) :
    (drain (m := Model F) fam n).run s = ((), drainS fam n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drain, drainS, Model.run_bind, run_step]
    cases h : s.queue.isEmpty with
    | true => rfl
    | false => simp only [Bool.not_false, ite_true, ih, Bool.false_eq_true, ite_false]

end Engine
