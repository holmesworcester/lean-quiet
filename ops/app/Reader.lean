/-
The reader: what the frame wants read (the conversation's ids, its
rows), read on a connection of its own, one read transaction a pass, and
put on the board (Live.Board). The frame takes the board's values and
reads nothing of the store for them, so a slow read makes a value late,
never a frame slow (docs/PERF.md).

A pass takes the journal's rows and the frame's own notices (its
outbox's changes), netted and matched against the windows its reads
watch (Data.Live.notice: exactly the reads whose windows changed go
stale), forgets the wants the frame no longer has (and, when the wants
change, the windows of every read none of them holds: the reads it
watches are exactly its wants' own), and reads
again each want one of whose reads went stale, or that it does not hold,
at most `cap` of them, in the frame's order (the visible first). An
equal value leaves the board unchanged (`Board.put`). The pass's cache is
a `Live`, so LiveLaws holds of it on this connection: every value a pass
puts is of the pass's one moment.

On a device the passes run on a thread of their own (`run`); without
one (the headless twins) the frame runs a pass itself, at the points it
would take the board.
-/
import engine.renderer.Board
import ops.community.message.View
import ops.community.Intents

namespace Reader
open Engine Community Data

/-- What the frame wants read. -/
inductive Want where
  /-- A window of c's conversation: the `above` readable messages at and
  older than the anchor and the `below` newer than it; with no anchor,
  the newest `above`. A refill reads O(above + below) rows, however long
  the conversation (Heights' `window_rows`). -/
  | window (c : Id) (anchor : Option Pos) (above below : Nat)
  /-- Message m's row in c, as `me` sees it (Kinds.Message.read). -/
  | row (c me m : Id)
  deriving DecidableEq, Hashable

/-- What a want reads as. -/
inductive Val where
  /-- The window's positions, newest first; how many readable messages
  are newer than it and older than it (counted, not read), and in all. -/
  | window (ids : Array Pos) (newer older total : Nat)
  /-- The row, or none while its message cannot be shown. -/
  | row (d : Option Row.RowData)
  deriving BEq

/-- What the frame and the reader share. -/
structure Shared where
  board : IO.Ref (_root_.Live.Board Want Val)
  /-- The frame's wants, most urgent first. -/
  wants : IO.Ref (Array Want)
  /-- The frame's outbox, as of its last frame. -/
  out : IO.Ref (Array Pending)
  /-- The rows the frame's own writes filed (to its outbox) since the
  last pass. -/
  notes : IO.Ref (Array Filing)
  /-- The journal's rows the reader has taken (the writer prunes below
  the frame's and this). -/
  seen : IO.Ref Nat

def Shared.new : IO Shared :=
  return ⟨← IO.mkRef {}, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0⟩

structure St where
  rd : Db
  live : Live := {}
  out : Array Pending := #[]
  seen : Nat := 0
  /-- Each held want's reads: it is read again when one goes stale. -/
  deps : Std.HashMap Want (Array Q) := {}
  /-- Wants to read again: marked when a pass's notices stale one of
  their reads, before any is read again (two wants reading one list
  both see its change), and kept until read. -/
  dirty : Std.HashSet Want := {}
  passes : Nat := 0
  /-- The wants of the last pass: when they change, the reads no want
  holds stop being watched. -/
  last : Array Want := #[]

abbrev RM := StateT St IO

/-- A read through the pass's cache (App's `read`, on this connection). -/
def read (q : Q) : RM Ans := do
  let s ← get
  if let some a := s.live.answer q then return a
  let a ← q.run s.rd s.out
  modify fun s => { s with live := s.live.store q a }
  return a

instance : Reads RM := ⟨read⟩

/-- A want's value, and the reads it made. -/
def eval : Want → RM (Val × Array Q)
  -- the window counts the messages beside it (each read's inRange): its
  -- reads are marked counted, so each watches its range (ListQ.watch)
  | .window c none above _ => do
    let (a, deps) ← readView (Community.readable c (limit := some above)).counting #[]
    return (.window (a.rows.map (·.1)).toArray 0 (a.inRange - min a.inRange a.rows.length) a.inRange, deps)
  | .window c (some p) above below => do
    -- at and older than p (one byte past its id: p itself is in), and newer
    let (o, deps) ← readView (Community.readable c (limit := some above) (before := some (p.1, p.2.push 0))).counting #[]
    let (n, deps) ← readView (Community.readable c (limit := some below) (desc := false) (after := some p)).counting deps
    let ids := (n.rows.reverse ++ o.rows).map (·.1)
    return (.window ids.toArray (n.inRange - min n.inRange n.rows.length) (o.inRange - min o.inRange o.rows.length)
      (n.inRange + o.inRange), deps)
  | .row c me m => do
    match ← Kinds.Message.read c me m with
    | some (d, deps) => return (.row (some d), deps)
    -- not shown yet: no reads held, so it is read again each pass
    | none => return (.row none, #[])

/-- Whether w's reads changed: not held, or one of its reads stale
(`Live.staleW`, the model's: engine/renderer/ReaderLaws.lean). -/
def stale (s : St) (w : Want) : Bool :=
  _root_.Live.staleW (fun q => !s.live.fresh q) (fun w => (s.deps[w]?).map (·.toList)) w

/-- One pass, in one read transaction; whether it put anything or took
any change. -/
def pass (sh : Shared) (cap : Nat := 64) : RM Bool := do
  let wants ← sh.wants.get
  let out ← sh.out.get
  let notes ← sh.notes.modifyGet fun a => (a, #[])
  let rd := (← get).rd
  rd.exec "BEGIN"
  try
    let s ← get
    -- the journal, read first: the commits this pass's reads see
    let (fs, vs, top) ← rd.filingsSince s.seen
    let want : Std.HashSet Want := wants.foldl (·.insert ·) {}
    -- the store's rows and the outbox's are netted apart: a row the store
    -- files as it leaves the outbox is two changes (stored, no longer
    -- pending), not one undone
    modify fun s => { s with seen := top, out, live := (s.live.notice fs (vs.map (·.1))).notice notes,
                             deps := s.deps.filter fun w _ => want.contains w,
                             dirty := s.dirty.filter want.contains, passes := s.passes + 1 }
    sh.seen.set top
    -- mark every want whose reads changed, before reading any again,
    -- then read the first `cap` marked in the frame's order: the model's
    -- decisions (Live.mark, Live.pick), so RWorld.inv_pass and settle
    -- are about this pass
    let s ← get
    let marked := _root_.Live.mark wants.toList (stale s) s.dirty.toList
    let todo := _root_.Live.pick wants.toList marked cap
    modify fun s => { s with dirty := marked.foldl (·.insert ·) {} }
    let mut puts : Array (Want × Val) := #[]
    for w in todo do
      let (v, deps) ← eval w
      modify fun s => { s with deps := s.deps.insert w deps, dirty := s.dirty.erase w }
      puts := puts.push (w, v)
    rd.exec "COMMIT"
    -- when the wants changed, forget the cached reads no want holds, and
    -- stop watching their windows (Screen.screen_subs: what is watched is
    -- what the wants read)
    if (← get).last != wants then
      let held := (← get).deps.fold (fun acc _ qs => qs.foldl (fun a q => a.insert q) acc) ({} : Std.HashSet Q)
      modify fun s => { s with live := s.live.keep held.contains, last := wants }
    sh.board.modify fun b => puts.foldl (fun b (w, v) => b.put w v) (b.keep want.contains)
    return !puts.isEmpty || !fs.isEmpty || !vs.isEmpty
  catch e =>
    rd.exec "ROLLBACK"
    throw e

/-- The reader's thread: a pass, and a short rest when it found nothing. -/
partial def run (sh : Shared) (s : St) : IO Unit := do
  let s ← try
      let (busy, s) ← (pass sh).run s
      if !busy then IO.sleep 2
      pure s
    catch e => do
      IO.eprintln s!"reader: {e}"
      IO.sleep 50
      pure s
  run sh s

end Reader
