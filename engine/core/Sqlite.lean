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
holds. A purge (`purgeSql`) is one too: the engine's `purge`, which
finds dependents through `reqs`, each stored op's requirements (the
model reads them off its ops). Afterwards it rebuilds the file (`VACUUM`)
and truncates the WAL, so no file keeps a deleted byte; that changes no
row (`scrubSql`). `secure_delete`, on for every connection, zeroes the
cells deletes free.
-/
import engine.core.Core
import engine.core.Codec
import engine.core.Model

namespace Engine

opaque DbPointed : NonemptyType
def Db : Type := DbPointed.type
instance : Nonempty Db := DbPointed.property

@[extern "le_sql_open"] opaque Db.open (path : @& String) : IO Db
@[extern "le_sql_exec"] opaque Db.exec (db : @& Db) (sql : @& String) : IO Unit
@[extern "le_sql_query"] opaque Db.query (db : @& Db) (sql : @& String) (args : @& Array ByteArray) :
  IO (Array (Array ByteArray))

def schemaCore : String := "
PRAGMA secure_delete = ON;
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
CREATE TABLE IF NOT EXISTS ops (id BLOB PRIMARY KEY, bytes BLOB NOT NULL) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS catalog (seq INTEGER PRIMARY KEY AUTOINCREMENT, id BLOB NOT NULL UNIQUE);
CREATE TABLE IF NOT EXISTS catalog_version (version INTEGER PRIMARY KEY);
CREATE TABLE IF NOT EXISTS retry_cursor (peer BLOB PRIMARY KEY, bytes BLOB NOT NULL) WITHOUT ROWID;
CREATE TRIGGER IF NOT EXISTS catalog_insert AFTER INSERT ON ops BEGIN
  INSERT INTO catalog (id) VALUES (NEW.id);
END;
CREATE TRIGGER IF NOT EXISTS catalog_delete AFTER DELETE ON ops BEGIN
  DELETE FROM catalog WHERE id = OLD.id;
END;
CREATE TABLE IF NOT EXISTS reqs (req BLOB NOT NULL, op BLOB NOT NULL, PRIMARY KEY (req, op)) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS status (id BLOB PRIMARY KEY, verdict BLOB NOT NULL) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS waits (blocker BLOB NOT NULL, waiter BLOB NOT NULL, UNIQUE (blocker, waiter));
CREATE INDEX IF NOT EXISTS waits_blocker ON waits (blocker);
CREATE INDEX IF NOT EXISTS waits_waiter ON waits (waiter);
CREATE TABLE IF NOT EXISTS queue (seq INTEGER PRIMARY KEY AUTOINCREMENT, id BLOB NOT NULL);
CREATE TABLE IF NOT EXISTS idx (k BLOB NOT NULL, s BLOB NOT NULL, id BLOB NOT NULL, UNIQUE (k, id));
CREATE INDEX IF NOT EXISTS idx_ks ON idx (k, s, id);
CREATE INDEX IF NOT EXISTS idx_id ON idx (id);
CREATE TABLE IF NOT EXISTS cnt (k BLOB PRIMARY KEY, n INTEGER NOT NULL) WITHOUT ROWID;
CREATE TRIGGER IF NOT EXISTS idx_count AFTER INSERT ON idx BEGIN
  INSERT INTO cnt (k, n) VALUES (NEW.k, 1) ON CONFLICT (k) DO UPDATE SET n = n + 1;
END;
CREATE TRIGGER IF NOT EXISTS idx_uncount AFTER DELETE ON idx BEGIN
  UPDATE cnt SET n = n - 1 WHERE k = OLD.k;
  DELETE FROM cnt WHERE k = OLD.k AND n <= 0;
END;
CREATE TABLE IF NOT EXISTS tally (k TEXT PRIMARY KEY, n INTEGER NOT NULL) WITHOUT ROWID;
CREATE TRIGGER IF NOT EXISTS tally_ops_insert AFTER INSERT ON ops BEGIN
  UPDATE tally SET n = n + 1 WHERE k = 'ops';
  UPDATE tally SET n = n + 1 WHERE k = 'undecided' AND NOT EXISTS (SELECT 1 FROM status WHERE id = NEW.id);
END;
CREATE TRIGGER IF NOT EXISTS tally_ops_delete AFTER DELETE ON ops BEGIN
  UPDATE tally SET n = n - 1 WHERE k = 'ops';
  UPDATE tally SET n = n - 1 WHERE k = 'undecided' AND NOT EXISTS (SELECT 1 FROM status WHERE id = OLD.id);
END;
CREATE TRIGGER IF NOT EXISTS tally_status_insert BEFORE INSERT ON status BEGIN
  UPDATE tally SET n = n - 1 WHERE k = 'undecided'
    AND EXISTS (SELECT 1 FROM ops WHERE id = NEW.id) AND NOT EXISTS (SELECT 1 FROM status WHERE id = NEW.id);
END;
CREATE TRIGGER IF NOT EXISTS tally_status_delete AFTER DELETE ON status BEGIN
  UPDATE tally SET n = n + 1 WHERE k = 'undecided' AND EXISTS (SELECT 1 FROM ops WHERE id = OLD.id);
END;
CREATE TRIGGER IF NOT EXISTS tally_queue_insert AFTER INSERT ON queue BEGIN
  UPDATE tally SET n = n + 1 WHERE k = 'queue';
END;
CREATE TRIGGER IF NOT EXISTS tally_queue_delete AFTER DELETE ON queue BEGIN
  UPDATE tally SET n = n - 1 WHERE k = 'queue';
END;
"

/-- The three counts a write turn's budget reads (`budgetSql`), set from
the tables themselves when a database has no tally rows yet (new,
wiped, or older than the tally); the `tally` triggers keep them exact
from then on, so a turn reads three rows, not three scans of the store.
An open that finds the rows only reads them: the app reopens its store
often (the reader about once a second), and seeding on every open took
the write lock and scanned the store each time (tests/app/headless.sh:
writes slowed past its timeouts). -/
def tallySeed : String := "
BEGIN IMMEDIATE;
INSERT OR REPLACE INTO tally (k, n) VALUES
  ('ops', (SELECT count(*) FROM ops)),
  ('undecided', (SELECT count(*) FROM ops WHERE NOT EXISTS (SELECT 1 FROM status WHERE status.id = ops.id))),
  ('queue', (SELECT count(*) FROM queue));
COMMIT;
"

/-- The guard stays inside the transaction as well: concurrent first opens
may both see an absent version, but only one backfill takes effect. -/
def catalogMigration : String := "
BEGIN IMMEDIATE;
INSERT OR IGNORE INTO catalog (id)
  SELECT id FROM ops WHERE NOT EXISTS (SELECT 1 FROM catalog_version WHERE version = 1) ORDER BY id;
INSERT OR IGNORE INTO catalog_version (version) VALUES (1);
COMMIT;
"

/-- Full initialization, retained for explicit legacy-schema migration. -/
def schema : String := schemaCore ++ catalogMigration

def Db.openAt (path : String) : IO Db := do
  let db ← Db.open path
  db.exec schemaCore
  let version ← db.query "SELECT version FROM catalog_version WHERE version = 1" #[]
  if version.isEmpty then db.exec catalogMigration
  let tally ← db.query "SELECT k FROM tally" #[]
  if tally.size != 3 then db.exec tallySeed
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

/-- A count, read with one statement. -/
def countSql (sql : String) : SqlM F Nat := do
  let rows ← sqlQ (F := F) sql #[]
  return match rows[0]? >>= (·[0]?) with
    | some b => (String.fromUTF8? b >>= String.toNat?).getD 0
    | none => 0

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
  dependents x := do return col0 (← sqlQ "SELECT op FROM reqs WHERE req = ? ORDER BY op" #[x])
  undecide x := do
    sqlDo "DELETE FROM status WHERE id = ?" #[x]
    sqlDo "DELETE FROM idx WHERE id = ?" #[x]
    sqlDo "DELETE FROM queue WHERE id = ?" #[x]
  deleteOp x := do
    let o : Option Op ← sqlOne "op" (← sqlQ "SELECT bytes FROM ops WHERE id = ?" #[x])
    if let some o := o then
      for r in o.reqs do sqlDo "DELETE FROM reqs WHERE req = ? AND op = ?" #[r, x]
    sqlDo "DELETE FROM ops WHERE id = ?" #[x]
    sqlDo "DELETE FROM waits WHERE blocker = ?" #[x]
    sqlDo "DELETE FROM waits WHERE waiter = ?" #[x]
  countOps := countSql "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'ops'"

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

/-- The judging steps the tables need at most (Engine.budget): the
queue's length, plus the undecided stored ops times the stored ops,
read from the `tally` rows: three point reads, whatever the store holds
(tests/engine/Differential.lean and Purge.lean check them against the
tables, across writes, judging, purges and a reopen). -/
def budgetSql : SqlM F Nat := do
  let q ← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'queue'"
  let u ← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'undecided'"
  let n ← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'ops'"
  return q + u * n

/-- The same three counts, scanned from the tables: what the tally rows
must equal (the tests' oracle; nothing on the running path reads it). -/
def budgetScan : SqlM F (Nat × Nat × Nat) := do
  let q ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM queue"
  let u ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM ops WHERE id NOT IN (SELECT id FROM status)"
  let n ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM ops"
  return (q, u, n)

/-- The tally rows: queue, undecided, stored. -/
def tallyRows : SqlM F (Nat × Nat × Nat) := do
  let q ← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'queue'"
  let u ← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'undecided'"
  let n ← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'ops'"
  return (q, u, n)

/-- One write turn, atomically: the capped turn (`turnCapped`: the job
and its urgent closure judged ahead, then at most `drainCap` queued;
engine/core/TurnLaws.lean). An idle turn (no ops) with nothing queued
takes no write lock. -/
def receive [Codec F] [SortKey F] (fam : Family F) (ops : List Op) : SqlM F Unit := do
  if ops.isEmpty then
    if (← countSql (F := F) "SELECT CAST(n AS TEXT) FROM tally WHERE k = 'queue'") == 0 then return
  transact do
    let _ ← turnCapped (m := SqlM F) fam drainCap ops

/-! ## Purging -/

/-- Add a versioned set of derived indexes without rewriting ops or verdicts.
Used before starting a node's reader/writer threads. The migration and marker
commit together; interruption rolls both back. Pages bound working memory,
and INSERT OR IGNORE keeps both old filings and count triggers idempotent. -/
def reindexOnce [Codec F] [SortKey F] (version : String) (keys : F → List ByteArray)
    (retryInvalid : Option (Family F) := none) : SqlM F Bool := do
  let db ← getDb
  db.exec "CREATE TABLE IF NOT EXISTS index_versions (version BLOB PRIMARY KEY) WITHOUT ROWID"
  let done : SqlM F Bool := do
    return !(← sqlQ "SELECT version FROM index_versions WHERE version = ?" #[version.toUTF8]).isEmpty
  if ← done then return false
  transact do
    if ← done then return false
    let n ← countSql (F := F) "SELECT CAST(count(*) AS TEXT) FROM status"
    let mut after : Option Id := none
    for _ in [0:n / 256 + 1] do
      let rows ← match after with
        | none => sqlQ "SELECT id, verdict FROM status ORDER BY id LIMIT 256" #[]
        | some id => sqlQ "SELECT id, verdict FROM status WHERE id > ? ORDER BY id LIMIT 256" #[id]
      if rows.isEmpty then break
      for row in rows do
        let some id := row[0]? | throw (IO.userError "index migration: missing id")
        let some bytes := row[1]? | throw (IO.userError "index migration: missing verdict")
        let some verdict := (Codec.decode bytes : Option (Verdict F))
          | throw (IO.userError "index migration: undecodable verdict")
        if let .valid fact := verdict then
          for key in keys fact do
            sqlDo "INSERT OR IGNORE INTO idx (k, s, id) VALUES (?, ?, ?)" #[key, SortKey.sortOf fact, id]
        else if retryInvalid.isSome then
          -- An older validator may have refused a newly supported op and
          -- its dependents. Retry together; never discard their op bytes.
          sqlDo "DELETE FROM status WHERE id = ?" #[id]
          Store.push (F := F) id
        after := some id
    if let some fam := retryInvalid then
      drain (m := SqlM F) fam (← budgetSql (F := F))
    sqlDo "INSERT INTO index_versions (version) VALUES (?)" #[version.toUTF8]
    return true

/-- The purge itself, inside a transaction: the engine's `purge`, then
judging to rest. A walk that does not end means the tables disagree, and
the purge aborts. -/
def purgeTx [Codec F] [SortKey F] (fam : Family F) (ids : List Id) : SqlM F (List Id) := do
  let some gone ← purgeCapped (m := SqlM F) fam drainCap ids
    | throw (IO.userError "purge: the dependents walk did not end")
  return gone

/-- Copy the WAL into the database and truncate it, so no old frame
keeps a deleted byte. Outside any transaction; a no-op unless the
database is in WAL mode. -/
def checkpointSql : SqlM F Unit := do
  let mode := col0 (← sqlQ (F := F) "PRAGMA journal_mode" #[])
  if (mode.head? >>= String.fromUTF8?) != some "wal" then return
  let rows ← sqlQ (F := F) "PRAGMA wal_checkpoint(TRUNCATE)" #[]
  if (rows[0]? >>= (·[0]?) >>= String.fromUTF8?) != some "0" then
    throw (IO.userError "purge: a reader blocked the WAL checkpoint; the purged bytes stay in the WAL until the next one")

/-- What a purge does after its transaction, to the file only: with
`vacuum`, `VACUUM`; then the WAL checkpoint. Neither changes a row of
any table (SQLite rebuilds the file from its rows, and copies the WAL
into it), so the tables are what the purge's transaction left, which
`purge_after` in tests/engine/Purge.lean checks. -/
def scrubSql (vacuum : Bool) : SqlM F Unit := do
  if vacuum then (← getDb).exec "VACUUM"
  checkpointSql

/-- **Purge `ids`** (Engine/Purge.lean): one transaction (`purgeTx`);
then, with `scrub` (the default), `scrubSql`: `VACUUM` and a truncating
checkpoint.

`secure_delete` zeroes the cells a delete frees, but not the copies a
b-tree leaves behind when it moves cells between pages: a page rebuilt
by a split keeps its old cells in the gap between its pointers and its
content, and `Tests/Purge.lean` finds a purged secret there. `VACUUM`
rebuilds the file from its live rows, so no copy survives; it costs a
rewrite of the database. A purge of ops that hold nothing secret (a
shipped courier) passes `scrub := false` and does not wait for readers
or truncate the WAL. A purge that deleted nothing (a session closed
twice) skips the `VACUUM`: no cell was freed. Purging again is harmless,
so a blocked checkpoint can be retried by purging again. -/
def purgeSql [Codec F] [SortKey F] (fam : Family F) (ids : List Id) (scrub : Bool := true) :
    SqlM F Unit := do
  let gone ← transact (purgeTx fam ids)
  if scrub then scrubSql (!gone.isEmpty)
  -- Public handshake couriers carry no secret. Requiring a truncating
  -- checkpoint here blocks behind UI snapshots and can kill the network
  -- task after the courier is deleted but before its bytes are sent.

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
