/-
The app's data: the engine on SQLite, read and written from two threads.

- **One writer.** A task of its own owns the write connection. It takes
  jobs (ops, with the blob bytes they name) from a queue, this node's own
  writes first, and commits each job as one transaction (`receive`). After
  each commit it reads the keys that commit filed (`takeFiled`) and posts
  them as notices.
- **Reads never wait for it.** The frame reads on its own connection
  (SQLite's WAL: a reader sees the last commit, and a long write never
  blocks it).
- **Live answers.** Every read is a query instance (`Q`). Reading one
  arms a one-shot watch on its key; a notice for that key disarms it and
  marks it stale; the next read runs the query again. Between two reads
  an instance is noticed at most once, however much changes
  (`Live.notice`), so a sync burst costs one read per instance on
  screen, not one per op.
- **Pending writes.** A write this node composes is judged at once, in
  memory, against decided facts (it may cite only those), and goes into
  the outbox. Every answer includes the outbox's facts, marked pending,
  until the commit that decides them: the same op, the same id.
-/
import Engine
import Community
import Quiet.Platform
import Std.Data.HashMap

namespace Data
open Engine Community Codec

def C := ed25519
def fam := family C

/-- Microseconds of the monotonic clock. -/
def nowUs : IO UInt64 := do return (← IO.monoNanosNow).toUInt64 / 1000

/-! ## The database -/

def appSchema : String := "
CREATE TABLE IF NOT EXISTS blobs (hash BLOB PRIMARY KEY, bytes BLOB NOT NULL) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v BLOB NOT NULL) WITHOUT ROWID;
"

def openDb (path : String) : IO Db := do
  let db ← Db.openAt path
  db.exec appSchema
  return db

def Db.meta (db : Db) (k : String) : IO (Option ByteArray) := do
  let rows ← db.query "SELECT v FROM meta WHERE k = ?" #[k.toUTF8]
  return rows[0]? >>= (·[0]?)

def Db.setMeta (db : Db) (k : String) (v : ByteArray) : IO Unit := do
  let _ ← db.query "INSERT OR REPLACE INTO meta (k, v) VALUES (?, ?)" #[k.toUTF8, v]

def Db.blob (db : Db) (hash : ByteArray) : IO (Option ByteArray) := do
  let rows ← db.query "SELECT bytes FROM blobs WHERE hash = ?" #[hash]
  return rows[0]? >>= (·[0]?)

/-! ## The writer -/

/-- A write: ops, and the bytes of the blobs they name (stored only if
their hash matches). -/
structure Job where
  ops : List Op
  blobs : List ByteArray := []
  mine : Bool := false
  deriving Inhabited

structure Writer where
  jobs : IO.Ref (Array Job)
  /-- Keys filed by commits since the frame last took them. -/
  notices : IO.Ref (Array ByteArray)
  /-- How many jobs are queued or running. -/
  busy : IO.Ref Nat
  /-- Commit times, µs, for the stats. -/
  commits : IO.Ref (Array (Nat × Nat))
  /-- While set, the writer takes no jobs (a test's or a demo's busy
  writer: what is written meanwhile stays pending). -/
  paused : IO.Ref Bool

def Writer.submit (w : Writer) (j : Job) : IO Unit := do
  w.busy.modify (· + 1)
  w.jobs.modify fun js => if j.mine then #[j] ++ js else js.push j

def Writer.takeNotices (w : Writer) : IO (Array ByteArray) := w.notices.modifyGet fun ns => (ns, #[])

def Writer.run1 (w : Writer) (db : Db) (j : Job) : IO Unit := do
  let t0 ← nowUs
  db.exec "BEGIN IMMEDIATE"
  try
    for b in j.blobs do
      let _ ← db.query "INSERT OR IGNORE INTO blobs (hash, bytes) VALUES (?, ?)" #[sha256 b, b]
    db.exec "COMMIT"
  catch e => db.exec "ROLLBACK"; throw e
  (receive fam j.ops).run db
  let filed ← db.takeFiled
  let t1 ← nowUs
  w.notices.modify (· ++ filed.toArray)
  w.commits.modify fun cs => (if cs.size > 200 then cs.extract 100 cs.size else cs).push
    (j.ops.length, (t1 - t0).toNat)

partial def Writer.loop (w : Writer) (db : Db) : IO Unit := do
  let next ← if ← w.paused.get then pure none else
    w.jobs.modifyGet fun js => if js.isEmpty then (none, js) else (some js[0]!, js.extract 1 js.size)
  match next with
  | none => IO.sleep 2; w.loop db
  | some j =>
    try w.run1 db j
    catch e => IO.eprintln s!"writer: {e}"
    w.busy.modify (· - 1)
    w.loop db

def Writer.start (path : String) : IO Writer := do
  let db ← openDb path
  db.watchFiled
  let w : Writer := ⟨← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef false⟩
  let _ ← IO.asTask (prio := .dedicated) (w.loop db)
  return w

/-! ## Queries and answers -/

/-- A read: one op's verdict, a list, or blob bytes (immutable once
there; watched on the blob op's decision). -/
inductive Q where
  | get (x : Id)
  | list (q : ListQ)
  | facts (q : ListQ)
  | bytes (op hash : ByteArray)
  deriving BEq, Hashable, Inhabited

/-- What a read answers. `pending`: the outbox's, not yet committed. -/
inductive Ans where
  | fact (v : Option Fact) (pending : Bool)
  | list (a : Answer) (pending : List Id)
  | facts (a : Answer) (fs : List Fact)
  | bytes (b : Option ByteArray)
  deriving Inhabited, BEq

instance : BEq Fact := ⟨fun a b => decide (a = b)⟩

/-- The key whose filing can change q's answer (one key: a coarser key is
allowed, a narrower one never). -/
def Q.watch : Q → ByteArray
  | .get x => opKey x
  | .list q => q.key
  | .facts q => q.key
  | .bytes op _ => opKey op

/-! ## The outbox -/

/-- A write composed here, judged, and not yet committed. -/
structure Pending where
  op : Op
  fact : Fact
  keys : List ByteArray

def Pending.pos (p : Pending) : Pos := (sortOf p.fact, p.op.id)

/-- The outbox's facts merged into a store answer: rows under the
query's keys, inside its range, not in the store yet. -/
def overlayList (out : Array Pending) (q : ListQ) (a : Answer) : Answer × List Id := Id.run do
  let mine := out.toList.filter fun p =>
    p.keys.contains q.key && q.also.all (p.keys.contains ·) && !(a.rows.any (·.2 == p.op.id))
  if mine.isEmpty then return (a, [])
  let inR := mine.filter fun p => q.inside p.pos
  let sorted := sortPos (a.rows ++ inR.map Pending.pos)
  let rows := if q.desc then sorted.reverse else sorted
  let rows := if q.limit = 0 then [] else rows.take q.limit
  -- a pending row pushed past the limit is left out like any other
  return (⟨rows, a.inRange + inR.length, a.total + mine.length⟩, mine.map (·.op.id))

/-! ## Live answers -/

structure Entry where
  ans : Ans
  stale : Bool
  deriving Inhabited

/-- Every instance read, its answer and whether a notice made it stale;
the armed watches by key. -/
structure Live where
  entries : Std.HashMap Q Entry := {}
  armed : Std.HashMap ByteArray (Array Q) := {}
  reads : Nat := 0
  deriving Inhabited

/-- A notice: the instances armed on these keys go stale and disarm. -/
def Live.notice (l : Live) (keys : Array ByteArray) : Live := Id.run do
  let mut l := l
  for k in keys do
    match l.armed[k]? with
    | none => pure ()
    | some qs =>
      l := { l with armed := l.armed.erase k }
      for q in qs do
        if let some e := l.entries[q]? then
          l := { l with entries := l.entries.insert q { e with stale := true } }
  return l

/-- Whether q has an answer that no notice has made stale. -/
def Live.fresh (l : Live) (q : Q) : Bool := match l.entries[q]? with
  | some e => !e.stale
  | none => false

/-- Record q's answer just read, and arm its watch. -/
def Live.store (l : Live) (q : Q) (a : Ans) : Live :=
  let k := q.watch
  { l with
    entries := l.entries.insert q ⟨a, false⟩
    armed := l.armed.insert k ((l.armed.getD k #[]).push q)
    reads := l.reads + 1 }

/-- Forget instances nobody reads any more (their watches stay armed
until noticed, harmlessly). -/
def Live.keep (l : Live) (want : Q → Bool) : Live :=
  { l with entries := l.entries.filter fun q _ => want q }

/-- The store's answer to q on the read connection, with the outbox. -/
def Q.run (db : Db) (out : Array Pending) : Q → IO Ans
  | .get x => do
    let v ← (getSql (F := Fact) x).run db
    match v with
    | some (.valid f) => return .fact (some f) false
    | some .invalid => return .fact none false
    | none => match out.find? (·.op.id == x) with
      | some p => return .fact (some p.fact) true
      | none => return .fact none false
  | .list q => do
    let a ← (listSql (F := Fact) q).run db
    let (a, pend) := overlayList out q a
    return .list a pend
  | .facts q => do
    let (a, fs) ← (listFactsSql (F := Fact) q).run db
    let (a, pend) := overlayList out q a
    let extra := out.toList.filter (fun p => pend.contains p.op.id) |>.map (·.fact)
    return .facts a (fs ++ extra)
  | .bytes _ hash => return .bytes (← Data.Db.blob db hash)

end Data
