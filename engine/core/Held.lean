/-
A store as plain data, so a node can run without SQLite: the ops taken
in, in order, and the engine's tables (`DB`). Reads and writes are the
model's (`Model`), lifted; a write turn ingests and then drains with
the proven budget (`budget log db`, so `drain_bounded` applies).

`Turn` is one write turn, in whatever store a node runs on: SQLite's
`receive`, or this.
-/
import engine.core.Sqlite
import engine.core.Budget
import engine.core.Query
import engine.core.Purge

namespace Engine.Sync

/-- One write turn: take in ops (already through an intake) and judge
everything that became decidable. And forgetting: purge ops (with the
dependents purge takes; `Engine.Purge`), then judge again what that
un-decided. `scrub` also rewrites the file so the bytes are gone from
disk (a session's secrets); a courier needs no scrub. -/
class Turn (F : Type) (m : Type → Type) where
  turn : Family F → List Op → m Unit
  purge : Family F → List Id → Bool → m Unit

instance {F} [Codec F] [SortKey F] : Turn F (SqlM F) where
  turn := receive
  purge fam ids scrub := do
    purgeSql fam ids scrub
    receive fam []

/-- A store as data: the ops taken in, and the tables. -/
structure Held (F : Type) where
  log : List Op := []
  db : DB F := DB.empty

def HeldM (F : Type) (α : Type) := Held F → α × Held F

instance {F} : Monad (HeldM F) where
  pure a := fun h => (a, h)
  bind m k := fun h => k (m h).1 (m h).2

def HeldM.run {F α} (m : HeldM F α) (h : Held F) : α × Held F := m h

/-- A model step on the tables. -/
def lift {F α} (m : Model F α) : HeldM F α := fun h =>
  let r := m.run h.db
  (r.1, { h with db := r.2 })

instance {F} : Store F (HeldM F) where
  getOp x := lift (Store.getOp (F := F) x)
  putOp o := lift (Store.putOp (F := F) o)
  getStatus x := lift (Store.getStatus (F := F) x)
  setStatus x v := lift (Store.setStatus (F := F) x v)
  addWait r x := lift (Store.addWait (F := F) r x)
  waiters r := lift (Store.waiters (F := F) r)
  clearWaiters r := lift (Store.clearWaiters (F := F) r)
  push x := lift (Store.push (F := F) x)
  pop := lift (Store.pop (F := F))
  index k x := lift (Store.index (F := F) k x)
  lookup k := lift (Store.lookup (F := F) k)

instance {F} [SortKey F] : Lists F (HeldM F) where
  list q := lift (Lists.list q)

/-- A write turn on held data: ingest, then drain with the budget read
off the tables (`drain_bounded`: it empties the queue). -/
instance {F} : Turn F (HeldM F) where
  turn fam ops := fun h =>
    let log := h.log ++ ops
    let s := ops.foldl (fun s o => ingestS o s) h.db
    ((), { log, db := drainS fam (budget log s) s })
  purge fam ids _ := fun h =>
    -- `Reach.purge`: the log keeps what purge kept; then drain again.
    let log := h.log.filter fun o => !has (purgeSet fam h.db ids) o.id
    let s := purgeS fam ids h.db
    ((), { log, db := drainS fam (budget log s) s })

end Engine.Sync
