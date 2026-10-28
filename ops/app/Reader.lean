/-
The reader: what the frame wants read (the conversation's ids, its
rows), read on a connection of its own, one read transaction a pass, and
put on the board (Live.Board). The frame takes the board's values and
reads nothing of the store for them, so a slow read makes a value late,
never a frame slow (docs/PERF.md).

A pass takes the journal's rows and the frame's own notices (its
outbox's changes), forgets the wants the frame no longer has, and reads
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
  /-- The conversation of c: its newest `limit` readable messages. -/
  | ids (c : Id) (limit : Nat)
  /-- Message m's row in c, as `me` sees it (Kinds.Message.read). -/
  | row (c me m : Id)
  deriving DecidableEq, Hashable

/-- What a want reads as. -/
inductive Val where
  /-- The messages' positions, newest first, how many came, and how many
  there are. -/
  | ids (ids : Array Pos) (fetched total : Nat)
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
  /-- The keys the frame's own writes filed since the last pass. -/
  notes : IO.Ref (Array ByteArray)
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
  passes : Nat := 0

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
  | .ids c n => do
    let (a, deps) ← readView (Community.readable c (limit := some n)) #[]
    return (.ids (a.rows.map (·.1)).toArray a.rows.length a.total, deps)
  | .row c me m => do
    match ← Kinds.Message.read c me m with
    | some (d, deps) => return (.row (some d), deps)
    -- not shown yet: no reads held, so it is read again each pass
    | none => return (.row none, #[])

/-- Whether w is to be read again: not held, or one of its reads stale. -/
def dirty (s : St) (w : Want) : Bool :=
  match s.deps[w]? with
  | none => true
  | some qs => qs.isEmpty || qs.any fun q => !s.live.fresh q

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
    let (ks, top) ← rd.changesSince s.seen
    let want : Std.HashSet Want := wants.foldl (·.insert ·) {}
    modify fun s => { s with seen := top, out, live := s.live.notice (ks ++ notes),
                             deps := s.deps.filter fun w _ => want.contains w, passes := s.passes + 1 }
    sh.seen.set top
    let mut puts : Array (Want × Val) := #[]
    for w in wants do
      if puts.size ≥ cap then break
      if dirty (← get) w then
        let (v, deps) ← eval w
        modify fun s => { s with deps := s.deps.insert w deps }
        puts := puts.push (w, v)
    rd.exec "COMMIT"
    -- now and then, forget the cached reads no want holds
    if (← get).passes % 256 == 0 then
      let held := (← get).deps.fold (fun acc _ qs => qs.foldl (fun a q => a.insert q) acc) ({} : Std.HashSet Q)
      modify fun s => { s with live := s.live.keep held.contains }
    sh.board.modify fun b => puts.foldl (fun b (w, v) => b.put w v) (b.keep want.contains)
    return !puts.isEmpty || !ks.isEmpty
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
