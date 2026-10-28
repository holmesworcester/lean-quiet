/-
`Store` on SQLite: each table of the model (Engine/Model.lean) is a
table here, and each value is stored as its `Codec.encode` bytes, read
back through `Codec.decode` (`decode_encode` proves the round trip).
Set-like lists are rowid-ordered, as the model appends; the queue is
ordered by seq. So with an untampered database a run here returns what
the same run returns on the model: that refinement is the one thing
not proven, and tests/differential.sh checks it.

One write turn is one `BEGIN IMMEDIATE` transaction (`transact`), so a
crash leaves the tables as of the last commit, a state where `Inv`
holds. A purge (`purgeSql`) is one too. It finds dependents through
`reqs`, each stored op's requirements (the model reads them off its
ops), and afterwards rebuilds the file (`VACUUM`) and truncates the WAL,
so no file keeps a deleted byte. `secure_delete`, on for every
connection, zeroes the cells deletes free.
-/
import engine.core.Core
import engine.core.Codec
import engine.core.Model
import Std.Data.HashSet

namespace Engine

opaque DbPointed : NonemptyType
def Db : Type := DbPointed.type
instance : Nonempty Db := DbPointed.property

@[extern "le_sql_open"] opaque Db.open (path : @& String) : IO Db
@[extern "le_sql_exec"] opaque Db.exec (db : @& Db) (sql : @& String) : IO Unit
@[extern "le_sql_query"] opaque Db.query (db : @& Db) (sql : @& String) (args : @& Array ByteArray) :
  IO (Array (Array ByteArray))

def schema : String := "
PRAGMA secure_delete = ON;
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
CREATE TABLE IF NOT EXISTS ops (id BLOB PRIMARY KEY, bytes BLOB NOT NULL) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS reqs (req BLOB NOT NULL, op BLOB NOT NULL, PRIMARY KEY (req, op)) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS status (id BLOB PRIMARY KEY, verdict BLOB NOT NULL) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS waits (blocker BLOB NOT NULL, waiter BLOB NOT NULL, UNIQUE (blocker, waiter));
CREATE INDEX IF NOT EXISTS waits_blocker ON waits (blocker);
CREATE TABLE IF NOT EXISTS queue (seq INTEGER PRIMARY KEY AUTOINCREMENT, id BLOB NOT NULL);
CREATE TABLE IF NOT EXISTS idx (k BLOB NOT NULL, s BLOB NOT NULL, id BLOB NOT NULL, UNIQUE (k, id));
CREATE INDEX IF NOT EXISTS idx_ks ON idx (k, s, id);
CREATE TABLE IF NOT EXISTS cnt (k BLOB PRIMARY KEY, n INTEGER NOT NULL) WITHOUT ROWID;
CREATE TRIGGER IF NOT EXISTS idx_count AFTER INSERT ON idx BEGIN
  INSERT INTO cnt (k, n) VALUES (NEW.k, 1) ON CONFLICT (k) DO UPDATE SET n = n + 1;
END;
CREATE TRIGGER IF NOT EXISTS idx_uncount AFTER DELETE ON idx BEGIN
  UPDATE cnt SET n = n - 1 WHERE k = OLD.k;
  DELETE FROM cnt WHERE k = OLD.k AND n <= 0;
END;
"

def Db.openAt (path : String) : IO Db := do
  let db ← Db.open path
  db.exec schema
  return db

/-- Store F on a database: one connection, read by every statement. -/
def SqlM (F : Type) (α : Type) := ReaderT Db IO α

instance {F} : Monad (SqlM F) := inferInstanceAs (Monad (ReaderT Db IO))
instance {F} : MonadLift IO (SqlM F) := inferInstanceAs (MonadLift IO (ReaderT Db IO))
instance {F} : MonadExceptOf IO.Error (SqlM F) := inferInstanceAs (MonadExceptOf IO.Error (ReaderT Db IO))

def SqlM.run {F α} (m : SqlM F α) (db : Db) : IO α := m db
def getDb {F} : SqlM F Db := fun db => pure db

variable {F : Type}

def sqlQ (sql : String) (args : Array ByteArray) : SqlM F (Array (Array ByteArray)) := do
  (← getDb).query sql args

def sqlDo (sql : String) (args : Array ByteArray) : SqlM F Unit := do
  let _ ← sqlQ (F := F) sql args

/-- The one value a lookup returns, decoded; a row that does not decode
means the database was tampered with. -/
def sqlOne {α} [Codec α] (what : String) (rows : Array (Array ByteArray)) : SqlM F (Option α) :=
  match rows[0]? with
  | none => pure none
  | some row => match row[0]? >>= Codec.decode with
    | some a => pure (some a)
    | none => throw (IO.userError s!"undecodable {what} row")

def col0 (rows : Array (Array ByteArray)) : List ByteArray :=
  rows.toList.filterMap (·[0]?)

/-- Where a fact sorts among the rows filed under one key: compared as
bytes (memcmp), ties broken by id. The model needs no sort key (its
lists are sets); queries over it sort by this same function. -/
class SortKey (F : Type) where
  sortOf : F → ByteArray

/-- The sort key of op x's fact, read back from the verdict `decide` has
just written (an Invalid or missing verdict sorts first). -/
def sortOfStatus [Codec F] [SortKey F] (x : Id) : SqlM F ByteArray := do
  let v : Option (Verdict F) ← sqlOne "verdict" (← sqlQ "SELECT verdict FROM status WHERE id = ?" #[x])
  return match v with
    | some (.valid f) => SortKey.sortOf f
    | _ => .empty

open Codec in
instance sqlStore [Codec F] [SortKey F] : Store F (SqlM F) where
  getOp x := do sqlOne "op" (← sqlQ "SELECT bytes FROM ops WHERE id = ?" #[x])
  putOp o := do
    sqlDo "INSERT INTO ops (id, bytes) VALUES (?, ?)" #[o.id, encode o]
    for r in o.reqs do sqlDo "INSERT OR IGNORE INTO reqs (req, op) VALUES (?, ?)" #[r, o.id]
  getStatus x := do sqlOne "verdict" (← sqlQ "SELECT verdict FROM status WHERE id = ?" #[x])
  setStatus x v := sqlDo "INSERT OR REPLACE INTO status (id, verdict) VALUES (?, ?)" #[x, encode v]
  addWait r x := sqlDo "INSERT OR IGNORE INTO waits (blocker, waiter) VALUES (?, ?)" #[r, x]
  waiters r := do return col0 (← sqlQ "SELECT waiter FROM waits WHERE blocker = ? ORDER BY rowid" #[r])
  clearWaiters r := sqlDo "DELETE FROM waits WHERE blocker = ?" #[r]
  push x := sqlDo "INSERT INTO queue (id) VALUES (?)" #[x]
  pop := do
    return (col0 (← sqlQ "DELETE FROM queue WHERE seq = (SELECT min(seq) FROM queue) RETURNING id" #[])).head?
  index k x := do
    sqlDo "INSERT OR IGNORE INTO idx (k, s, id) VALUES (?, ?, ?)" #[k, ← sortOfStatus x, x]
  lookup k := do return col0 (← sqlQ "SELECT id FROM idx WHERE k = ? ORDER BY rowid" #[k])

/-- Run act as one transaction: all of it commits, or none of it. -/
def transact {α} (act : SqlM F α) : SqlM F α := do
  let db ← getDb
  db.exec "BEGIN IMMEDIATE"
  try
    let a ← act
    db.exec "COMMIT"
    return a
  catch e =>
    db.exec "ROLLBACK"
    throw e

/-- A count, read with one statement. -/
def countSql (sql : String) : SqlM F Nat := do
  let rows ← sqlQ (F := F) sql #[]
  return match rows[0]? >>= (·[0]?) with
    | some b => (String.fromUTF8? b >>= String.toNat?).getD 0
    | none => 0

/-- The judging steps the tables need at most (Engine.budget): the
queue's length, plus the undecided stored ops times the stored ops. -/
def budgetSql : SqlM F Nat := do
  let q ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM queue"
  let u ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM ops WHERE id NOT IN (SELECT id FROM status)"
  let n ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM ops"
  return q + u * n

/-- One write turn: take in ops and judge everything that became
decidable, atomically, with the proven `drain` and a budget read in the
same transaction (`drain_bounded`: it empties the queue). -/
def receive [Codec F] [SortKey F] (fam : Family F) (ops : List Op) : SqlM F Unit :=
  transact do
    for o in ops do ingest (m := SqlM F) o
    drain (m := SqlM F) fam (← budgetSql (F := F))

/-! ## Purging -/

/-- `ids` and every stored op that requires one of them, transitively
(the model's `closeUp`), walked through `reqs`. Each id enters the walk
once, so it ends within the stored ops plus `ids` steps; a walk that
does not means the tables disagree, and the purge aborts. -/
def closureSql (ids : List Id) : SqlM F (List Id) := do
  let n ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM ops"
  let mut seen : Std.HashSet Id := {}
  let mut found : Array Id := #[]
  for x in ids do
    if !seen.contains x then seen := seen.insert x; found := found.push x
  let mut i := 0
  for _ in [0:n + ids.length + 1] do
    if h : i < found.size then
      let x := found[i]
      i := i + 1
      for y in col0 (← sqlQ (F := F) "SELECT op FROM reqs WHERE req = ?" #[x]) do
        if !seen.contains y then seen := seen.insert y; found := found.push y
    else break
  if i < found.size then throw (IO.userError "purge: the dependents walk did not end")
  return found.toList

/-- The purge itself, inside a transaction: the model's `purgeS`, then
judging to rest. Every op of the closure loses its verdict, filings and
queue entries; its conn and local ops leave every table; its shared ops
are queued again in byte order and judged over what remains. -/
def purgeTx [Codec F] [SortKey F] (fam : Family F) (ids : List Id) : SqlM F Unit := do
  let mut gone : List Op := []
  let mut again : List Id := []
  for x in ← closureSql (F := F) ids do
    match ← Store.getStatus (F := F) x with
    | some (.valid f) =>
      for k in fam.fileKeys x f do sqlDo (F := F) "DELETE FROM idx WHERE k = ? AND id = ?" #[k, x]
    | _ => pure ()
    sqlDo (F := F) "DELETE FROM status WHERE id = ?" #[x]
    sqlDo (F := F) "DELETE FROM queue WHERE id = ?" #[x]
    match ← Store.getOp (F := F) x with
    | some o => if (fam.room o).isSome then again := x :: again else gone := o :: gone
    | none => pure ()
  for o in gone do
    sqlDo (F := F) "DELETE FROM ops WHERE id = ?" #[o.id]
    sqlDo (F := F) "DELETE FROM waits WHERE blocker = ?" #[o.id]
    for r in o.reqs do
      sqlDo (F := F) "DELETE FROM reqs WHERE req = ? AND op = ?" #[r, o.id]
      sqlDo (F := F) "DELETE FROM waits WHERE blocker = ? AND waiter = ?" #[r, o.id]
  for x in sortIds again do Store.push (F := F) x
  drain (m := SqlM F) fam (← budgetSql (F := F))

/-- Copy the WAL into the database and truncate it, so no old frame
keeps a deleted byte. Outside any transaction; a no-op unless the
database is in WAL mode. -/
def checkpointSql : SqlM F Unit := do
  let mode := col0 (← sqlQ (F := F) "PRAGMA journal_mode" #[])
  if (mode.head? >>= String.fromUTF8?) != some "wal" then return
  let rows ← sqlQ (F := F) "PRAGMA wal_checkpoint(TRUNCATE)" #[]
  if (rows[0]? >>= (·[0]?) >>= String.fromUTF8?) != some "0" then
    throw (IO.userError "purge: a reader blocked the WAL checkpoint; the purged bytes stay in the WAL until the next one")

/-- **Purge `ids`** (Engine/Purge.lean): one transaction; then, with
`scrub` (the default), `VACUUM`; then the checkpoint.

`secure_delete` zeroes the cells a delete frees, but not the copies a
b-tree leaves behind when it moves cells between pages: a page rebuilt
by a split keeps its old cells in the gap between its pointers and its
content, and `Tests/Purge.lean` finds a purged secret there. `VACUUM`
rebuilds the file from its live rows, so no copy survives; it costs a
rewrite of the database. A purge of ops that hold nothing secret (a
shipped courier) can pass `scrub := false`. Purging again is harmless,
so a blocked checkpoint can be retried by purging again. -/
def purgeSql [Codec F] [SortKey F] (fam : Family F) (ids : List Id) (scrub : Bool := true) :
    SqlM F Unit := do
  transact (purgeTx fam ids)
  if scrub then (← getDb).exec "VACUUM"
  checkpointSql

/-! ## Reading the whole database back, for tests -/

def dumpOps : SqlM F (List Op) := do
  let rows ← sqlQ (F := F) "SELECT bytes FROM ops ORDER BY id" #[]
  return rows.toList.filterMap fun r => r[0]? >>= Codec.decode

def dumpStatus [Codec F] : SqlM F (List (Id × Verdict F)) := do
  let rows ← sqlQ (F := F) "SELECT id, verdict FROM status ORDER BY id" #[]
  return rows.toList.filterMap fun r => do
    let x ← r[0]?
    let v ← r[1]? >>= Codec.decode
    pure (x, v)

def dumpWaits : SqlM F (List (Id × Id)) := do
  let rows ← sqlQ (F := F) "SELECT blocker, waiter FROM waits ORDER BY rowid" #[]
  return rows.toList.filterMap fun r => do pure ((← r[0]?), (← r[1]?))

def dumpQueue : SqlM F (List Id) := do
  return col0 (← sqlQ (F := F) "SELECT id FROM queue ORDER BY seq" #[])

def dumpIdx : SqlM F (List (ByteArray × Id)) := do
  let rows ← sqlQ (F := F) "SELECT k, id FROM idx ORDER BY rowid" #[]
  return rows.toList.filterMap fun r => do pure ((← r[0]?), (← r[1]?))

end Engine
