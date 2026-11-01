/- Actual local writes commit shared operation bytes before the handler returns.
The representation compatibility premises avoid assuming hash injectivity. -/
import ops.connection.StorageEffects
import ops.sync.SharedLog

namespace Connection.Execution
open Engine Engine.Sync

theorem M.getOp_apply (i : Id) (s : Memory) :
    (Store.getOp i : M _) s = (s.held.db.ops i, s) := rfl

theorem M.forIn_reads {α β} (l : List α) (b : β) (f : α → β → M (ForInStep β))
    (g : β → α → β) (s : Memory) (hf : ∀ a b, f a b s = (.yield (g b a), s)) :
    forIn l b f s = (l.foldl g b, s) := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih => rw [List.forIn_cons, M.bind_apply, hf]; exact ih _

/-- This is the same deduplicating writer, interpreted with entropy/retry
metadata alongside Held. The writer itself changes neither metadata field. -/
theorem write_store_tape (x : Sync F M) (n : Engine.Sync.Node) (s : Memory) (ops : List Op) :
    (n.write x ops s).2.held =
      (n.write ({ fam := x.fam, hooks := { rooms := fun _ => pure [], sealFor := plainSeal, openFrame := plainOpen } } : Sync F (HeldM F)) ops s.held).2 := by
  rw [write_store]
  unfold Node.write
  simp only [M.bind_apply]
  rw [M.forIn_reads (g := absentStep s.held.db)]
  · dsimp only
    generalize ops.foldl (absentStep s.held.db) [] = absent
    split
    · rfl
    · simp only [M.bind_apply]
      rw [M.forIn_reads (g := fileStep x.fam ((Turn.turn x.fam absent.reverse : M Unit) s).2.held.db)]
      · rfl
      · intro a b
        rw [M.bind_apply, M.getOp_apply]
        unfold fileStep
        split <;> rfl
  · intro a b
    unfold absentStep
    split
    · rw [M.bind_apply, M.getOp_apply]
      split <;> rfl
    · rfl

theorem write_receives (x : Sync F M) (n : Engine.Sync.Node) (s : Memory) (ops : List Op)
    (hi : Inv x.fam s.held.db) {o : Op} (ho : o ∈ ops)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.write x ops s).2.held.db.ops o.id = some o := by
  rw [write_store_tape]
  exact write_takes _ n s.held ops hi ho sameInput sameStore

theorem write_log_agrees_tape (x : Sync F M) (n : Engine.Sync.Node) (s : Memory) (ops : List Op)
    (hi : Inv x.fam s.held.db) (ha : s.held.LogAgrees) : (n.write x ops s).2.held.LogAgrees := by
  rw [write_store_tape]
  exact write_log_agrees _ n s.held ops hi ha

/-- Once a shared operation is committed, all ordinary runtime effects
in a continuation retain it, including reactions and session purges. -/
theorem committed_bind {α β} (fam : Family F) (p : M α) (k : α → M β) (s : Memory)
    {o : Op} (ho : (p s).2.held.db.ops o.id = some o) (hs : (fam.room o).isSome)
    (hk : ∀ a, GoesM fam (k a)) : ((p >>= k) s).2.held.db.ops o.id = some o :=
  (hk _ _).shared_retained ho hs

/-- The complete Node.store continuation retains the operation it just
committed, including all sixteen possible actual reaction rounds. -/
theorem store_receives (x : Sync F M) (hr : NodeTape.ReadOnly x)
    (n : Engine.Sync.Node) (s : Memory) (ops : List Op)
    (hi : Inv x.fam s.held.db) {o : Op} (ho : o ∈ ops) (hs : (x.fam.room o).isSome)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.store x ops true s).2.held.db.ops o.id = some o := by
  have hp : (n.put x ops true s).2.held.db.ops o.id = some o := by
    simpa only [Node.put, intake, ite_true] using write_receives x n s ops hi ho sameInput sameStore
  unfold Node.store
  apply committed_bind x.fam _ _ s hp hs
  intro r
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  goesTape [NodeTape.fanout_goes x hr, NodeTape.put_goes, hr.react.goes]

/-- A local write has committed every compatible shared input before
Node.onWrite returns. This is a completed-handler bound, not a wall-clock
bound or a claim that absent prerequisites already exist. -/
theorem onWrite_receives (x : Sync F M) (hr : NodeTape.ReadOnly x)
    (n : Engine.Sync.Node) (s : Memory) (ops : List Op) (now : Nat)
    (hi : Inv x.fam s.held.db) {o : Op} (ho : o ∈ ops) (hs : (x.fam.room o).isSome)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.onWrite x ops now s).2.held.db.ops o.id = some o := by
  unfold Node.onWrite
  exact committed_bind x.fam _ _ s
    (store_receives x hr n s ops hi ho hs sameInput sameStore) hs
    (fun _ => NodeTape.finish_goes x hr _ _ _)

theorem production_write_receives (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (s : Memory) (ops : List Op) (now : Nat) (hi : Inv family s.held.db)
    {o : Op} (ho : o ∈ ops) (hs : (family.room o).isSome)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.step (S.sync side) (.write ops) now s).2.held.db.ops o.id = some o := by
  simpa only [Node.step] using
    (onWrite_receives (S.sync side) (NodeTape.production_readOnly S side) n s ops now hi ho hs sameInput sameStore)

end Connection.Execution
