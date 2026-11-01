/-
**What the proofs trust about SQLite, in one place.** This is the
store's trust file, as engine/core/Trust.lean is the crypto's. The
assumption is a named `Prop`, never an `axiom`: a law that needs it
takes it as a premise, so `#print axioms` stays at Lean's three.

The engine's code is generic over its tables (`Store`,
engine/core/Core.lean). The proofs run it on the model
(engine/core/Model.lean). The app runs the same code on SQLite
(engine/core/Sqlite.lean). This contract links the two: SQLite holds
the model's tables, and each operation changes them as the model's
operation does.

Lean cannot check this contract. The SQLite calls are I/O, and Lean
sees an I/O action only as a function of an opaque world. So the
contract can be stated, but not proven. It is tested from both sides:
- The running code keeps it: tests/engine/Differential.lean (random
  workloads, every table row for row), QueryDiff.lean (list queries),
  Purge.lean (purges, `VACUUM` and checkpoint), and
  tests/vacuity/StoreTrust.lean (each operation alone, on a real file).
- It has content: in tests/vacuity/StoreTrust.lean the model's own store
  keeps its shape, and a store that drops a write does not.

SQLite keeps more than the five tables the dumps read: a counter per
key, the catalog, each op's requirements, each filing's sort key. (The
catalog's reads are in the contract, as changing no table; its rows are
not: a sweep's laws hold whatever positions it returns.) So the
contract does not say that any file whose rows look right behaves. It
says that some reading `holds` of a database as the model's tables
exists: every database the app opens holds some tables, a database that
holds tables shows them in its rows, and the operations keep it.

It is about correctness, not progress. SQLite may refuse an operation (a
full disk, a lock). The contract promises nothing about a refused
operation, except that a refused write turn (`transact`) changes no row.

It is meant for a file only this code has written, but that scope is not
in the formal statement: `opens` covers every file `Db.openAt` opens, so
the Prop is false of a corrupted or edited file. That files are not
corrupted or edited is an assumption about the environment, stated here
in prose only.
-/
import engine.core.Query
import engine.core.Catalog

namespace Trust
open Engine

variable {F : Type}

/-! ## The rows, as the dumps read them -/

/-- SQLite's five tables, as the dump functions (`dumpOps`, …) read
them back: ops by id; verdicts by id; waits, index rows and the queue in
the order they were written. -/
structure Rows (F : Type) where
  ops : List Op
  status : List (Id × Verdict F)
  waits : List (Id × Id)
  queue : List Id
  idx : List (ByteArray × Id)

/-- The values filed under key `k`, in row order. -/
def under {κ α : Type} [DecidableEq κ] (rows : List (κ × α)) (k : κ) : List α :=
  rows.filterMap fun p => if p.1 = k then some p.2 else none

/-- **Rows show the model's tables**: the same stored ops, the same
verdicts, each op's waiters and each key's filings in the same order,
and the same queue. -/
def Rows.Show (r : Rows F) (s : DB F) : Prop :=
  (∀ x, s.ops x = r.ops.find? (fun o => decide (o.id = x))) ∧
  s.stored.Perm (r.ops.map (·.id)) ∧
  (∀ x, s.status x = (r.status.find? (fun p => decide (p.1 = x))).map (·.2)) ∧
  (∀ b, s.waits b = under r.waits b) ∧
  s.queue = r.queue ∧
  (∀ k, s.idx k = under r.idx k)

/-- Read the five tables. -/
def dump [Codec F] : SqlM F (Rows F) := do
  return ⟨← dumpOps, ← dumpStatus, ← dumpWaits, ← dumpQueue, ← dumpIdx⟩

/-- **In world `w`, database `db` shows the tables `s`**: the dumps,
read there, return rows that show `s`. -/
def ShowsAt [Codec F] (db : Db) (w : Void IO.RealWorld) (s : DB F) : Prop :=
  ∃ r w', (dump (F := F)) db w = .ok r w' ∧ r.Show s

/-! ## The operations -/

/-- One operation of `Store`, as data. -/
inductive StoreOp (F : Type) : Type → Type where
  | getOp (x : Id) : StoreOp F (Option Op)
  | putOp (o : Op) : StoreOp F Unit
  | getStatus (x : Id) : StoreOp F (Option (Verdict F))
  | setStatus (x : Id) (v : Verdict F) : StoreOp F Unit
  | addWait (r x : Id) : StoreOp F Unit
  | waiters (r : Id) : StoreOp F (List Id)
  | clearWaiters (r : Id) : StoreOp F Unit
  | push (x : Id) : StoreOp F Unit
  | pop : StoreOp F (Option Id)
  | index (k : ByteArray) (x : Id) : StoreOp F Unit
  | lookup (k : ByteArray) : StoreOp F (List Id)
  | dependents (x : Id) : StoreOp F (List Id)
  | undecide (x : Id) : StoreOp F Unit
  | deleteOp (x : Id) : StoreOp F Unit
  | countOps : StoreOp F Nat

/-- The operation, on any store. -/
def StoreOp.run {m : Type → Type} [Store F m] {α : Type} : StoreOp F α → m α
  | .getOp x => Store.getOp x
  | .putOp o => Store.putOp (F := F) o
  | .getStatus x => Store.getStatus x
  | .setStatus x v => Store.setStatus x v
  | .addWait r x => Store.addWait (F := F) r x
  | .waiters r => Store.waiters (F := F) r
  | .clearWaiters r => Store.clearWaiters (F := F) r
  | .push x => Store.push (F := F) x
  | .pop => Store.pop (F := F)
  | .index k x => Store.index (F := F) k x
  | .lookup k => Store.lookup (F := F) k
  | .dependents x => Store.dependents (F := F) x
  | .undecide x => Store.undecide (F := F) x
  | .deleteOp x => Store.deleteOp (F := F) x
  | .countOps => Store.countOps (F := F)

/-! ## The shape, for any store -/

/-- **A store answers as the model** (for any store whose states are
`σ`): from a state that shows tables `s`, an operation that returns
returns what the model's operation returns from `s`, and reaches a state
that shows the model's next tables. An operation that fails (`none`) is
not constrained. -/
def AnswersAsModel {σ : Type} (run : ∀ {α : Type}, StoreOp F α → σ → Option (α × σ))
    (shows : σ → DB F → Prop) : Prop :=
  ∀ {α : Type} (op : StoreOp F α) (t : σ) (s : DB F), shows t s →
    ∀ v t', run op t = some (v, t') →
      v = (op.run (m := Model F) s).1 ∧ shows t' (op.run (m := Model F) s).2

/-! ## SQLite's -/

/-- An operation on the SQLite store, from world `w`: its answer and
the next world, or `none` if SQLite refused it. -/
def sqlStep [Codec F] [SortKey F] (db : Db) {α : Type} (op : StoreOp F α) (w : Void IO.RealWorld) :
    Option (α × Void IO.RealWorld) :=
  match (op.run (m := SqlM F)) db w with
  | .ok v w' => some (v, w')
  | .error _ _ => none

/-- The world an I/O action ends in, whether it returned or failed. -/
def worldOf {ε σ α : Type} : EST.Out ε σ α → Void σ
  | .ok _ w => w
  | .error _ w => w

/-- The budget `budgetSql` counts, on the model's tables: the queue, plus
the undecided stored ops times the stored ops. -/
def budgetOf (s : DB F) : Nat :=
  s.queue.length + (s.stored.filter fun y => (s.status y).isNone).length * s.stored.length

/-- `budgetOf`, read on the model: what `budgetSql` reads on SQLite. -/
def budgetM : Model F Nat := fun s => (budgetOf s, s)

/-- **A read changes no table** (for any store whose states are `σ`):
from a state that shows tables `s`, a read that returns leaves a state
that still shows `s`. What it returns is not constrained. -/
def ReadOnly {σ α : Type} (run : σ → Option (α × σ)) (shows : σ → DB F → Prop) : Prop :=
  ∀ t s, shows t s → ∀ v t', run t = some (v, t') → shows t' s

/-- An action on the SQLite store, from world `w`: its answer and the
next world, or `none` if SQLite refused it. -/
def sqlAct (db : Db) {α : Type} (x : SqlM F α) (w : Void IO.RealWorld) :
    Option (α × Void IO.RealWorld) :=
  match x db w with
  | .ok v w' => some (v, w')
  | .error _ _ => none

/-- **`x` on SQLite runs as `y` on the model**: from a world where the
database holds tables `s`, if `x` returns, it returns what `y` returns
from `s`, and the database then holds the tables `y` leaves. -/
def Sim [Codec F] (holds : Db → Void IO.RealWorld → DB F → Prop) {α : Type} (x : SqlM F α)
    (y : Model F α) : Prop :=
  ∀ db w s, holds db w s → ∀ v w', x db w = .ok v w' → v = (y s).1 ∧ holds db w' (y s).2

/-- **SQLite answers as the model.** `holds db w s` reads database `db`,
in world `w`, as the model's tables `s`. The contract:
- every database the app opens holds some tables;
- a database that holds tables shows them in its rows (the dumps);
- each store operation that returns answers as the model's, and the
  database then holds the model's next tables;
- beginning and committing a transaction change no table;
- a refused write turn (`transact`) changes no table;
- the budget query counts the model's tables;
- each list query answers as `eval` on the model's tables, and changes
  no table;
- a purge's `VACUUM` and checkpoint change no table, whether they
  finish or not;
- the catalog's two reads (`Catalog.sql`: its ceiling, a position's
  row), which the sweep runs, change no table. What they return is not
  constrained: the sweep's laws hold for every ceiling and row. -/
structure SqliteStore (F : Type) [Codec F] [SortKey F] (holds : Db → Void IO.RealWorld → DB F → Prop) :
    Prop where
  opens : ∀ path w db w', (Db.openAt path) w = .ok db w' → ∃ s, holds db w' s
  shows : ∀ db w s, holds db w s → ShowsAt db w s
  answers : ∀ db, AnswersAsModel (sqlStep (F := F) db) (holds db)
  brackets : ∀ sql ∈ ["BEGIN IMMEDIATE", "COMMIT"], ∀ db w s, holds db w s →
    ∀ w', (db.exec sql) w = .ok () w' → holds db w' s
  rollback : ∀ {α : Type} (act : SqlM F α) db w s, holds db w s →
    ∀ e w', (transact act) db w = .error e w' → holds db w' s
  budget : Sim holds (budgetSql (F := F)) budgetM
  lists : ∀ q, Sim holds (listSql (F := F) q) (fun s => (eval s q, s))
  scrub : ∀ vacuum db w s, holds db w s → holds db (worldOf ((scrubSql (F := F) vacuum) db w)) s
  catalog : ∀ db, ReadOnly (sqlAct db (Engine.Sync.Catalog.sql (F := F)).ceiling) (holds db) ∧
    ∀ seq, ReadOnly (sqlAct db ((Engine.Sync.Catalog.sql (F := F)).read seq)) (holds db)

end Trust
