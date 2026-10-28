/-
A store, counted (docs/PERF.md). `CostT m` over any store's monad
(SQLite, the engine's model, held data, a world of nodes) is a store
too, whose every door is charged: the call (a point read, a list, a
write) and what SQLite does for it under the SQLite assumption
(engine/core/Cost.lean, `levels`): the seeks into its B-trees and the
rows it steps over after them. Code written over `[Store F m] [Lists F m]`
runs counted with no change, and a budget stated with `Within` or
`Costs` holds for every store.

Where code runs (`SqlM`, `Model`, `HeldM`), `Tick` is free: code over
`[Tick m]` charges nothing there, and compiles to what it was.

What each door costs SQLite (engine/core/Sqlite.lean, Query.lean):

| door | statement | seeks | rows |
|---|---|---|---|
| getOp, getStatus | primary key | 1 | 0 |
| putOp, setStatus, addWait, push | insert | 1 | 0 |
| index | insert into idx, bump its counter | 2 | 0 |
| waiters, lookup | primary-key range | 1 | the list's length |
| clearWaiters | delete a primary-key range | 1 | 0 (its rows were read by waiters) |
| pop | the queue's first row, deleted | 2 | 0 |
| list | `listSql`: counters (1 + also), rows (1, and 1 per row for its verdict), the range count (1) | 3 + also + rows | rows + the range count, and with `also` the smallest conjunct's count |

A list with `also` is charged its total for the conjunct walk; SQLite
walks the smallest conjunct, which can be longer, so no law may rest on
that row of the table (no list the app or the node reads has `also`).
-/
import engine.core.Cost
import engine.core.Held
import engine.core.Families

namespace Engine
open CostT

/-! ## Where code runs, nothing is counted -/

instance {F : Type} : Tick (SqlM F) := Tick.free
instance {F : Type} : Tick (Model F) := Tick.free
instance {F : Type} : Tick (Sync.HeldM F) := Tick.free

/-! ## A store, counted -/

/-- What a list costs SQLite, from its answer (the table above). -/
def listCost {F : Type} (q : ListQ) (a : Answer F) : Meter :=
  { lists := 1
    seeks := 3 + q.also.length + a.rows.length + (if q.also.isEmpty then 0 else 1 + a.total * q.also.length)
    rows := a.rows.length + a.inRange + (if q.also.isEmpty then 0 else a.total) }

section
variable {F : Type} {m : Type → Type} [Monad m]

instance [Store F m] : Store F (CostT m) where
  getOp x := charged { reads := 1, seeks := 1 } (Store.getOp x)
  putOp o := charged { writes := 1, seeks := 1 } (Store.putOp (F := F) o)
  getStatus x := charged { reads := 1, seeks := 1 } (Store.getStatus x)
  setStatus x v := charged { writes := 1, seeks := 1 } (Store.setStatus x v)
  addWait r x := charged { writes := 1, seeks := 1 } (Store.addWait (F := F) r x)
  waiters r := chargedBy (fun ws => { reads := 1, seeks := 1, rows := ws.length }) (Store.waiters (F := F) r)
  clearWaiters r := charged { writes := 1, seeks := 1 } (Store.clearWaiters (F := F) r)
  push x := charged { writes := 1, seeks := 1 } (Store.push (F := F) x)
  pop := charged { reads := 1, writes := 1, seeks := 2 } (Store.pop (F := F))
  index k x := charged { writes := 1, seeks := 2 } (Store.index (F := F) k x)
  lookup k := chargedBy (fun xs => { reads := 1, seeks := 1, rows := xs.length }) (Store.lookup (F := F) k)

instance [Lists F m] : Lists F (CostT m) where
  list q := chargedBy (listCost q) (Lists.list q)

instance [Sync.Turn F m] : Sync.Turn F (CostT m) where
  turn fam ops := charged { writes := ops.length } (Sync.Turn.turn fam ops)
  purge fam ids scrub := charged { writes := ids.length } (Sync.Turn.purge fam ids scrub)

instance [Fresh m] : Fresh (CostT m) := ⟨lift Fresh.fresh⟩

end

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Store F m]
  {g : Meter → Nat}

theorem within_getOp (x : Id) : Within g (g { reads := 1, seeks := 1 }) (Store.getOp x : CostT m _) :=
  within_charged _ _

theorem within_getStatus (x : Id) :
    Within g (g { reads := 1, seeks := 1 }) (Store.getStatus x : CostT m _) :=
  within_charged _ _

end

end Engine
