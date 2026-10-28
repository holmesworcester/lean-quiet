/-
A store, counted (docs/PERF.md). `CostT m` over any store's monad
(SQLite, the engine's model, held data, a world of nodes) is a store
too, whose every door is charged: a point read (an op, a status, a
waiter list, an index lookup, the queue's head), a list query, a row
written, the ops of a write turn and the ids of a purge. Code written
over `[Store F m] [Lists F m]` runs counted with no change, and a budget
stated with `Within` holds for every store.
-/
import engine.core.Cost
import engine.core.Held
import engine.core.Families

namespace Engine
open CostT

section
variable {F : Type} {m : Type → Type} [Monad m]

instance [Store F m] : Store F (CostT m) where
  getOp x := charged { reads := 1 } (Store.getOp x)
  putOp o := charged { writes := 1 } (Store.putOp (F := F) o)
  getStatus x := charged { reads := 1 } (Store.getStatus x)
  setStatus x v := charged { writes := 1 } (Store.setStatus x v)
  addWait r x := charged { writes := 1 } (Store.addWait (F := F) r x)
  waiters r := charged { reads := 1 } (Store.waiters (F := F) r)
  clearWaiters r := charged { writes := 1 } (Store.clearWaiters (F := F) r)
  push x := charged { writes := 1 } (Store.push (F := F) x)
  pop := charged { reads := 1, writes := 1 } (Store.pop (F := F))
  index k x := charged { writes := 1 } (Store.index (F := F) k x)
  lookup k := charged { reads := 1 } (Store.lookup (F := F) k)

instance [Lists F m] : Lists F (CostT m) where
  list q := charged { lists := 1 } (Lists.list q)

instance [Sync.Turn F m] : Sync.Turn F (CostT m) where
  turn fam ops := charged { writes := ops.length } (Sync.Turn.turn fam ops)
  purge fam ids scrub := charged { writes := ids.length } (Sync.Turn.purge fam ids scrub)

instance [Fresh m] : Fresh (CostT m) := ⟨lift Fresh.fresh⟩

end

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Store F m]
  {g : Meter → Nat}

theorem within_getOp (x : Id) : Within g (g { reads := 1 }) (Store.getOp x : CostT m _) :=
  within_charged _ _

theorem within_getStatus (x : Id) : Within g (g { reads := 1 }) (Store.getStatus x : CostT m _) :=
  within_charged _ _

end

end Engine
