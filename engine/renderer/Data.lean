/-
The app's data: the engine on SQLite, read and written from two threads.

- **One writer.** A task of its own owns the write connection. It takes
  jobs (ops) from a queue, this node's own
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
import engine.core.Engine
import ops.community.Community
import ops.connection.All
import engine.renderer.Platform
import Std.Data.HashMap

namespace Data
open Engine Community Codec

def C := ed25519

/-- What the store holds: the community's facts and the connection
family's (Connection.F); the app reads and draws the community's. -/
abbrev SF := Connection.F

/-- The node's one family: Community's and Connection's, composed. -/
def fam : Family SF := Connection.node C Connection.sodium

/-- Microseconds of the monotonic clock. -/
def nowUs : IO UInt64 := do return (← IO.monoNanosNow).toUInt64 / 1000

/-! ## The database -/

def openDb (path : String) : IO Db := Db.openAt path

/-! ## The writer -/

/-- A write: ops (a file's bytes are ops too: its chunks). -/
structure Job where
  ops : List Op
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
  -- a peer's job keeps only shared ops: a local-only op is this node's
  -- own write, whatever peers send (Engine.Sync: intake_local, stored_local)
  (receive fam (intake fam j.mine j.ops)).run db
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

/-! ## Queries and answers

Every read is a list (Engine.Query): one fact is the list under its own
id's key (`Q.get`), so a component's subscriptions are exactly the keys of
the lists it reads (Engine.eval_stable: a list's answer changes only if a
row is filed under its key). The one other read is an op's own bytes
(a chunk's slice, a pending request's body), immutable, watched on the
op's key. -/

inductive Q where
  | list (q : ListQ)
  /-- An op as stored, whatever its verdict (this device's own undecided
  request, say): its bytes. -/
  | op (x : Id)
  deriving BEq, Hashable, Inhabited

/-- One fact: the list under its op's own key, at most one row. -/
def Q.get (x : Id) : Q := .list { key := opKey x, limit := some 1 }

/-- What a read answers; `pending` names rows from the outbox. -/
inductive Ans where
  | list (a : Answer Fact) (pending : List Id)
  | bytes (b : Option ByteArray)
  deriving Inhabited, BEq

/-- The key whose filing can change q's answer. -/
def Q.watch : Q → ByteArray
  | .list q => q.key
  | .op x => opKey x

/-! ## The outbox -/

/-- A write composed here, judged, and not yet committed. Its keys are the
fact's and its own id's, as the engine will file them. -/
structure Pending where
  op : Op
  fact : Fact
  keys : List ByteArray

def Pending.pos (p : Pending) : Pos := (sortOf p.fact, p.op.id)

/-- The outbox's ops a store answer to q has not counted yet: those
filed under q's keys that the store does not hold decided (`stored`, a
point read of each id: so a count-only read, with no rows to look in, is
exact too) and that are not among its rows. -/
def pendingFor (out : Array Pending) (q : ListQ) (a : Answer Fact) (stored : Id → Bool) : List Pending :=
  out.toList.filter fun p =>
    p.keys.contains q.key && q.also.all (p.keys.contains ·) && !stored p.op.id &&
      !(a.rows.any (·.1.2 == p.op.id))

/-- The outbox's facts merged into a store answer: rows under the
query's keys, inside its range, not in the store yet. -/
def overlayList (out : Array Pending) (q : ListQ) (a : Answer Fact) (stored : Id → Bool := fun _ => false) :
    Answer Fact × List Id := Id.run do
  let mine := pendingFor out q a stored
  if mine.isEmpty then return (a, [])
  let inR := mine.filter fun p => q.inside p.pos
  let all := a.rows ++ inR.map fun p => (p.pos, p.fact)
  let sorted := all.mergeSort fun x y => x.1.cmp y.1 != .gt
  let rows := q.cut (if q.desc then sorted.reverse else sorted)
  -- a pending row pushed past the limit is left out like any other
  return (⟨rows, a.inRange + inR.length, a.total + mine.length⟩, mine.map (·.op.id))

/-- **The overlay counts every op once.** Its total is the store's plus
the pending ops the store has not counted (`pendingFor`): one held both
stored and pending is counted once, by the store. -/
theorem overlay_total (out : Array Pending) (q : ListQ) (a : Answer Fact) (stored : Id → Bool) :
    (overlayList out q a stored).1.total = a.total + (pendingFor out q a stored).length := by
  unfold overlayList
  by_cases h : (pendingFor out q a stored).isEmpty
  · simp [h, List.isEmpty_iff.1 h]
  · simp [h]

/-! ## Live answers -/

structure Entry where
  ans : Ans
  stale : Bool
  deriving Inhabited

/-- Every instance read, its answer and whether a notice made it stale;
the armed watches by key (each instance armed at most once). -/
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

/-- Record q's answer just read, and arm its watch (once). -/
def Live.store (l : Live) (q : Q) (a : Ans) : Live :=
  let k := q.watch
  let qs := l.armed.getD k #[]
  { l with
    entries := l.entries.insert q ⟨a, false⟩
    armed := if qs.contains q then l.armed else l.armed.insert k (qs.push q)
    reads := l.reads + 1 }

/-- Forget instances nobody reads any more, and their watches. -/
def Live.keep (l : Live) (want : Q → Bool) : Live :=
  let armed := l.armed.fold (fun acc k qs =>
    let qs := qs.filter want
    if qs.isEmpty then acc else acc.insert k qs) {}
  { l with entries := l.entries.filter fun q _ => want q, armed }

/-- An op's verdict, from the store (the judge reads requirements this way). -/
def status (db : Db) (x : Id) : IO (Option (Verdict SF)) :=
  (Store.getStatus (F := SF) (m := SqlM SF) x).run db

/-- The store's answer to q on the read connection, with the outbox. -/
def Q.run (db : Db) (out : Array Pending) : Q → IO Ans
  | .list q => do
    let a ← (listSql (F := SF) q).run db
    -- a community list's rows are all community facts (its key is theirs)
    let a : Answer Fact := ⟨a.lefts, a.inRange, a.total⟩
    -- each pending op the store already holds decided is counted by the
    -- store, not again by the outbox (between a commit and the frame
    -- taking its notice, an op is in both)
    let mut held : List Id := []
    for p in out do
      if (← Data.status db p.op.id).isSome then held := p.op.id :: held
    let (a, pend) := overlayList out q a fun x => held.any (· == x)
    return .list a pend
  | .op x => return .bytes ((← (Store.getOp (F := SF) (m := SqlM SF) x).run db).map (·.bytes))

/-! ## Components' reads

A component reads only through `Reads.read`: a list (or an op's bytes),
answered live (cached, watched on the list's key, the outbox included).
Kinds (Quiet/Kinds) are written against this class, so they do not
depend on the app, and every read a component makes is one of its
subscriptions. -/

class Reads (m : Type → Type) where
  read : Q → m Ans

section
variable {m : Type → Type} [Monad m] [Reads m]

/-- A list's rows and the outbox ids among them; the queries read are
appended to deps. -/
def readList (q : ListQ) (deps : Array Q) : m (Answer Fact × List Id × Array Q) := do
  match ← Reads.read (Q.list q) with
  | .list a pend => return (a, pend, deps.push (.list q))
  | _ => return (⟨[], 0, 0⟩, [], deps.push (.list q))

/-- One fact (the list under its own id), whether it is pending, and deps. -/
def readFact (x : Id) (deps : Array Q) : m (Option Fact × Bool × Array Q) := do
  let (a, pend, deps) ← readList { key := opKey x, limit := some 1 } deps
  return (a.rows.head?.map (·.2), pend.contains x, deps)

/-- A view run through the reads (the live cache, outbox overlaid): its
answer and the lists it read. By `view_stable` the answer changes only
when one of those lists does, so it is re-evaluated from cached answers
until a notice lands on one. -/
def readView {α : Type} : View Fact α → Array Q → m (α × Array Q)
  | .pure a, deps => return (a, deps)
  | .list q k, deps => do
    let (a, _, deps) ← readList q deps
    readView (k a) deps

end


end Data
