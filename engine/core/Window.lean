/-
Windows: notices exact by construction.

A screen does not watch a key; it watches a window of a list: the rows
filed under a key between two positions (`Win`). A list read with a
limit is a window too: newest first, its window runs from its last row's
position up (`ListQ.win`), so a row filed below it is not in it.

**The journal.** Every commit, whoever makes it, records in the store
(`Db.filings`, triggers on the index) each row it files or unfiles: its
key and position, the position holding the row's id. A purge unfiles,
and the drain after it may file the same row again, so a reader that
takes several commits at once first nets them (`net`): a row filed and
unfiled an even number of times is where it was.

**Matching.** The subscriptions are indexed by key, and each key's
windows by the positions their ends name (`Slots`): the slot a position
falls in (below the first end, at one, between two, above the last) is
found by binary search and lists exactly the windows that hold it. A
filing costs a hash of its key and log₂ of its key's windows'
comparisons, then one step per window it hits (`find_cost`).

The laws (engine/core/WindowLaws.lean): a subscriber is notified exactly
when one of its windows changed (`notice_iff`), so never for a row
outside them and always for one inside; and a read's window changes
exactly when its answer does (`read_notice_iff`).
-/
import engine.core.Query
import engine.core.View
import engine.core.Cost
import Std.Data.HashMap

namespace Engine

/-! ## Windows -/

/-- One end of a window: a position, and whether the window holds it. -/
abbrev End := Pos × Bool

/-- A window: the rows filed under `key` from `lo` to `hi` (none:
unbounded). -/
structure Win where
  key : ByteArray
  lo : Option End := none
  hi : Option End := none
  deriving BEq, Hashable, Inhabited, DecidableEq

/-- Whether p is at or past a lower end. -/
def above : Option End → Pos → Bool
  | none, _ => true
  | some (q, incl), p => match p.cmp q with
    | .gt => true
    | .eq => incl
    | .lt => false

/-- Whether p is at or before an upper end. -/
def below : Option End → Pos → Bool
  | none, _ => true
  | some (q, incl), p => match p.cmp q with
    | .lt => true
    | .eq => incl
    | .gt => false

/-- Whether the window's range holds position p. -/
def Win.inside (w : Win) (p : Pos) : Bool := above w.lo p && below w.hi p

/-- Whether the window holds a row filed under k at p. -/
def Win.has (w : Win) (k : ByteArray) (p : Pos) : Bool := Decidable.decide (k = w.key) && w.inside p

/-- The whole of a key's list. -/
def Win.all (k : ByteArray) : Win := { key := k }

/-- **A read's window**: the part of its key's list its rows depend on,
given its answer a. It is the read's range, cut where its limit cut the
answer: newest first, from the answer's last row up; oldest first, up to
it. A row filed outside it (below a newest-50 answer, say) changes none
of the rows (`WindowLaws.read_rows_iff`). Counts (`inRange`, `total`)
depend on more: a read that uses them watches its whole key
(`Win.all`). -/
def ListQ.win {F : Type} (q : ListQ) (a : Answer F) : Win :=
  let lo := q.after.map (·, false)
  let hi := q.before.map (·, false)
  match q.limit, a.rows.getLast? with
  | some n, some (p, _) =>
    if a.rows.length = n then
      if q.desc then { key := q.key, lo := some (p, true), hi }
      else { key := q.key, lo, hi := some (p, true) }
    else { key := q.key, lo, hi }
  | _, _ => { key := q.key, lo, hi }

/-- A read's range as a window: what its range count counts. -/
def ListQ.rangeWin (q : ListQ) : Win :=
  { key := q.key, lo := q.after.map (·, false), hi := q.before.map (·, false) }

/-- **What a watch on a read must cover**, given its answer a:
- a count (limit 0), or a list of several keys: the whole key, as its
  total counts it (`Win.all`);
- a read whose range count is used (`counted`): its range;
- else its rows' window (`ListQ.win`).
`WindowRead.watch_stable`: if that window holds the same rows, the
answer is the same, but for the counts no reader uses (`ListQ.kept`). -/
def ListQ.watch {F : Type} (q : ListQ) (a : Answer F) : Win :=
  if q.limit == some 0 || !q.also.isEmpty then Win.all q.key
  else if q.counted then q.rangeWin
  else q.win a

/-- An answer as its watch covers it: a count keeps its counts; a counted
read, its range count; any other, its rows alone. -/
def ListQ.kept {F : Type} (q : ListQ) (a : Answer F) : Answer F :=
  if q.limit == some 0 || !q.also.isEmpty then a
  else if q.counted then { a with total := 0 }
  else { a with inRange := 0, total := 0 }

/-- A view whose reader uses every read's range count: each read marked
`counted`, so its watch covers its range. Nothing else changes: no read
looks at the mark (`WindowRead.eval_counting`). -/
def View.counting {F α : Type} : View F α → View F α
  | .pure a => .pure a
  | .list q k => .list { q with counted := true } fun a => (k a).counting

/-! ## The journal -/

/-- One row of the journal: a row filed (`on`) or unfiled under a key,
at a position. -/
structure Filing where
  key : ByteArray
  pos : Pos
  on : Bool
  deriving Inhabited, DecidableEq

/-- Records, in the store, every row any connection's commit files or
unfiles in the index, with its key and position, and every verdict
recorded or cleared (`k` null; `ev` 2 and 3), numbered in commit order:
the journal a reader takes inside its own read transaction. -/
def Db.filings (db : Db) : IO Unit := db.exec "
CREATE TABLE IF NOT EXISTS filings (seq INTEGER PRIMARY KEY AUTOINCREMENT, k BLOB, s BLOB, id BLOB NOT NULL, ev INTEGER NOT NULL);
CREATE TRIGGER IF NOT EXISTS filings_idx AFTER INSERT ON idx BEGIN
  INSERT INTO filings (k, s, id, ev) VALUES (NEW.k, NEW.s, NEW.id, 1);
END;
CREATE TRIGGER IF NOT EXISTS filings_unidx AFTER DELETE ON idx BEGIN
  INSERT INTO filings (k, s, id, ev) VALUES (OLD.k, OLD.s, OLD.id, 0);
END;
CREATE TRIGGER IF NOT EXISTS filings_status AFTER INSERT ON status BEGIN
  INSERT INTO filings (id, ev) VALUES (NEW.id, 2);
END;
CREATE TRIGGER IF NOT EXISTS filings_unstatus AFTER DELETE ON status BEGIN
  INSERT INTO filings (id, ev) VALUES (OLD.id, 3);
END;
"

/-- The journal after `seq`: its filings, the ops whose verdicts were
recorded (true) or cleared (false), and its newest seq (`seq` if none). -/
def Db.filingsSince (db : Db) (seq : Nat) : IO (Array Filing × Array (Id × Bool) × Nat) := do
  let rows ← db.query "SELECT CAST(seq AS TEXT), k, s, id, CAST(ev AS TEXT) FROM filings WHERE seq > CAST(? AS INTEGER) ORDER BY seq"
    #[(toString seq).toUTF8]
  let mut fs := #[]
  let mut vs := #[]
  let mut top := seq
  for r in rows do
    if let some n := r[0]? >>= (String.fromUTF8? ·) >>= String.toNat? then top := max top n
    let ev := r[4]? >>= (String.fromUTF8? ·) >>= String.toNat?
    match ev, r[1]?, r[2]?, r[3]? with
    | some 1, some k, some s, some x => fs := fs.push ⟨k, (s, x), true⟩
    | some 0, some k, some s, some x => fs := fs.push ⟨k, (s, x), false⟩
    | some 2, _, _, some x => vs := vs.push (x, true)
    | some 3, _, _, some x => vs := vs.push (x, false)
    | _, _, _, _ => pure ()
  return (fs, vs, top)

/-- Delete the journal's rows up to `seq` (taken by every reader). -/
def Db.pruneFilings (db : Db) (seq : Nat) : IO Unit := do
  let _ ← db.query "DELETE FROM filings WHERE seq <= CAST(? AS INTEGER)" #[(toString seq).toUTF8]

/-- Flip e's membership. -/
def toggle (m : Std.HashMap (ByteArray × Pos) Unit) (e : ByteArray × Pos) :
    Std.HashMap (ByteArray × Pos) Unit :=
  if m.contains e then m.erase e else m.insert e ()

/-- **What a batch changed**: the (key, position) pairs it filed or
unfiled an odd number of times. A row is filed only where it is not,
and unfiled only where it is, so these are exactly the rows that are
there after the batch and were not before, or the other way round
(`WindowLaws.run_exact`). -/
def net (J : Array Filing) : Array (ByteArray × Pos) :=
  (J.foldl (fun m e => toggle m (e.key, e.pos)) {}).keysArray

/-! ## Finding the windows that hold a position -/

/-- What comparing p with another position costs, in byte steps: at
most p's bytes, and one more per part. -/
def posWork (p : Pos) : Nat := p.1.size + p.2.size + 2

/-- The number of `b[lo:hi]`'s positions before p, plus lo: binary
search, one comparison a step. -/
def rankM {m : Type → Type} [Monad m] [Tick m] (b : Array Pos) (p : Pos) (lo hi : Nat) : m Nat :=
  if h : lo < hi then do
    tick { work := posWork p }
    if (b.getD ((lo + hi) / 2) default).cmp p == .lt then rankM b p ((lo + hi) / 2 + 1) hi
    else rankM b p lo ((lo + hi) / 2)
  else pure lo
termination_by hi - lo

/-- One key's windows, for finding those that hold a position: the
distinct positions their ends name, ascending (`bounds`), and for each
slot the windows that hold it (`cover`). Slot 2i is the gap below
`bounds[i]` (above `bounds[i-1]`), slot 2i+1 is `bounds[i]` itself, and
slot 2m (m bounds) is above them all. -/
structure Slots (S : Type) where
  bounds : Array Pos := #[]
  cover : Array (Array S) := #[]
  deriving Inhabited

/-- The slot of p among bounds b, i of them before it: at b[i] if p is
b[i], else the gap below b[i]. -/
def slotOf (b : Array Pos) (p : Pos) (i : Nat) : Nat :=
  if i < b.size && (b.getD i default).cmp p == .eq then 2 * i + 1 else 2 * i

/-- The windows of these that hold p. -/
def Slots.find {S : Type} {m : Type → Type} [Monad m] [Tick m] (sl : Slots S) (p : Pos) :
    m (Array S) := do
  let i ← rankM sl.bounds p 0 sl.bounds.size
  tick { work := posWork p }
  pure (sl.cover.getD (slotOf sl.bounds p i) #[])

/-- Positions in order, a non-strict comparison for sorting. -/
def posLe (p q : Pos) : Bool := p.cmp q != .gt

/-- A sorted list with each run of equal positions kept once. -/
def dedupSorted : List Pos → List Pos
  | a :: b :: t => if a.cmp b == .eq then dedupSorted (b :: t) else a :: dedupSorted (b :: t)
  | l => l

/-- The positions a set of windows' ends name. -/
def endsOf {S : Type} (ws : Array (S × Win)) : List Pos :=
  ws.toList.flatMap fun x => x.2.lo.toList.map (·.1) ++ x.2.hi.toList.map (·.1)

/-- Whether a lower end lies at or below every position of gap i (those
strictly between b[i-1] and b[i]). -/
def gapLo (b : Array Pos) (i : Nat) : Option End → Bool
  | none => true
  | some (q, _) => 0 < i && q.cmp (b.getD (i - 1) default) != .gt

/-- Whether an upper end lies at or above every position of gap i. -/
def gapHi (b : Array Pos) (i : Nat) : Option End → Bool
  | none => true
  | some (q, _) => i < b.size && (b.getD i default).cmp q != .gt

/-- Whether window w holds slot j of bounds b. -/
def covers (b : Array Pos) (j : Nat) (w : Win) : Bool :=
  if j % 2 = 1 then w.inside (b.getD (j / 2) default) else gapLo b (j / 2) w.lo && gapHi b (j / 2) w.hi

/-- One key's windows, indexed. -/
def Slots.build {S : Type} (ws : Array (S × Win)) : Slots S :=
  let b := (dedupSorted ((endsOf ws).mergeSort posLe)).toArray
  { bounds := b
    cover := Array.ofFn (n := 2 * b.size + 1) fun j => (ws.filter fun x => covers b j x.2).map (·.1) }

/-! ## The subscriptions -/

/-- Every subscriber's windows, by key, each key's indexed. -/
structure Subs (S : Type) where
  keys : Std.HashMap ByteArray (Array (S × Win) × Slots S) := {}
  deriving Inhabited

namespace Subs
variable {S : Type}

/-- Key k's windows become ws. -/
def set (I : Subs S) (k : ByteArray) (ws : Array (S × Win)) : Subs S :=
  if ws.isEmpty then ⟨I.keys.erase k⟩ else ⟨I.keys.insert k (ws, Slots.build ws)⟩

/-- Key k's windows. -/
def at_ (I : Subs S) (k : ByteArray) : Array (S × Win) := ((I.keys[k]?).map (·.1)).getD #[]

/-- x subscribes to window w. -/
def add (I : Subs S) (x : S) (w : Win) : Subs S := I.set w.key ((I.at_ w.key).push (x, w))

/-- Subscriptions from a list. -/
def ofList (l : List (S × Win)) : Subs S := l.foldl (fun I (x, w) => I.add x w) {}

/-- Forget the subscribers nobody wants any more; a key whose windows
all stay keeps its index. -/
def keep (I : Subs S) (want : S → Bool) : Subs S :=
  ⟨I.keys.filterMap fun _ e =>
    let ws := e.1.filter (want ·.1)
    if ws.isEmpty then none else if ws.size = e.1.size then some e else some (ws, Slots.build ws)⟩

/-- **The subscribers with a window holding a row filed under k at p.**
A hash of k, then a binary search of k's windows' ends. -/
def find {m : Type → Type} [Monad m] [Tick m] (I : Subs S) (k : ByteArray) (p : Pos) :
    m (Array S) := do
  tick { work := k.size + 1 }
  match I.keys[k]? with
  | none => pure #[]
  | some (_, sl) => sl.find p

/-- The subscribers a batch's net filings reach, each as often as one of
its windows is hit. -/
def notifyM {m : Type → Type} [Monad m] [Tick m] (I : Subs S) :
    List (ByteArray × Pos) → m (Array S)
  | [] => pure #[]
  | (k, p) :: rest => do
    let xs ← I.find k p
    tick { work := xs.size }
    let ys ← I.notifyM rest
    pure (xs ++ ys)

/-- The subscribers a batch reaches: its net filings matched. -/
def notify (I : Subs S) (J : Array Filing) : Array S := Id.run (I.notifyM (net J).toList)

end Subs

end Engine
