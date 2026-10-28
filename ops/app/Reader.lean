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
import ops.community.membership.AcceptedView
import ops.community.membership.RequestView
import ops.connection.Intents

namespace Reader
open Engine Community Data

/-- What the frame wants read. -/
inductive Want where
  /-- A window of c's conversation: the `above` readable messages at and
  older than the anchor and the `below` newer than it; with no anchor,
  the newest `above`. A refill reads O(above + below) rows, however long
  the conversation (Heights' `window_rows`). -/
  | window (c : Id) (anchor : Option Pos) (above below : Nat)
  /-- How many readable messages of c are newer than the anchor, and how
  many at or older than it (no anchor: all are older): counted, not read.
  They size the scroll extent beside the window (the page's own read,
  Screen's `chrome`), so a message filed outside the window notifies
  this want alone; the frame reads it after the rows. -/
  | count (c : Id) (anchor : Option Pos)
  /-- Message m's row in c, as `me` sees it (Kinds.Message.read). -/
  | row (c me m : Id)
  /-- An attachment's chunk ops' bytes, in order (as stored, or in the
  outbox): what its file is opened from, off the frame. -/
  | slices (chunks : List Id)
  /-- This device's communities (Kinds.Accepted.read). -/
  | comms
  /-- c's present members, each with its devices and name, and whether
  `user` is an admin of c. -/
  | members (c user : Id)
  /-- c's join requests no admission answers yet. -/
  | asking (c : Id)
  /-- How many present members c has. -/
  | people (c : Id)
  deriving DecidableEq, Hashable

/-- Two of this device's communities alike: every field but the device,
which its seed fixes (`dev_ok`). -/
instance : BEq Kinds.Accepted.Me := ⟨fun a b =>
  a.acc == b.acc && a.seed == b.seed && a.c == b.c && a.adm == b.adm && a.user == b.user &&
    a.name == b.name && a.joiningOp == b.joiningOp && a.dialing == b.dialing && a.removed == b.removed⟩

/-- What a want reads as. -/
inductive Val where
  /-- The window's positions, newest first, and how many of them are
  newer than its anchor. -/
  | window (ids : Array Pos) (newerRows : Nat)
  /-- The counts beside the anchor: newer than it, and at or older. -/
  | count (newer older : Nat)
  /-- The row, or none while its message cannot be shown. -/
  | row (d : Option Row.RowData)
  /-- The chunk ops' bytes, or none while one is not here. -/
  | slices (raw : Option (List ByteArray))
  | comms (all : Array Kinds.Accepted.Me)
  | members (ms : Array (Id × List Key × String)) (admin : Bool)
  | asking (rs : Array Kinds.Request.Data)
  | people (n : Nat)
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
  /-- The peers of the node's kept sessions, read every half second (a
  connection family's list: not a want of the board). -/
  peers : IO.Ref (List ByteArray)
  /-- Moves each time the frame sets `wants` to something new. -/
  gen : IO.Ref Nat
  /-- The writers' commits (the app's writer counts its own, the node's
  notify counts the node's): a pass that sees it unmoved, with no note,
  the same wants and nothing dirty, reads nothing (RestLaws.start_rest). -/
  commits : IO.Ref Nat

def Shared.new (commits : IO.Ref Nat) : IO Shared :=
  return ⟨← IO.mkRef {}, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0, ← IO.mkRef [], ← IO.mkRef 0,
    commits⟩

/-- The frame's wants, set; the generation moves only when they change,
so a reader at rest stays at rest (RestLaws.nextGen_same). -/
def Shared.setWants (sh : Shared) (ws : Array Want) : IO Unit := do
  let old ← sh.wants.get
  sh.gen.modify (_root_.Live.nextGen old ws)
  if old != ws then sh.wants.set ws

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
  /-- The communities last read: Kinds.Accepted.read keeps their devices. -/
  known : Array Kinds.Accepted.Me := #[]
  /-- When the session list was last read (ms). -/
  peersAt : Nat := 0
  /-- The wants of the last pass: when they change, the reads no want
  holds stop being watched. -/
  last : Array Want := #[]
  /-- The reverse index: each read, the wants that recorded it
  (RestLaws' `rev`, complete). -/
  rev : Std.HashMap Q (Array Want) := {}
  /-- The frame's wants as of `gen`. -/
  gen : Nat := 0
  wantSet : Std.HashSet Want := {}
  /-- The reads the want being read has made. -/
  log : Array Q := #[]
  /-- The writers' commit count as of the last journal read, and when
  that was (ms). -/
  seenC : Nat := 0
  readAt : Nat := 0

abbrev RM := StateT St IO

/-- A read through the pass's cache (App's `read`, on this connection). -/
def read (q : Q) : RM Ans := do
  modify fun s => { s with log := s.log.push q }
  let s ← get
  let (a, live) ← (Live.readWith (fun q => q.run s.rd s.out) q).run s.live
  modify fun s => { s with live }
  return a

instance : Reads RM := ⟨read⟩

/-- A want's value, and the reads it made. -/
def eval : Want → RM (Val × Array Q)
  -- the window's reads are rows alone: each watches its rows' window,
  -- which holds exactly its rows (WindowRead.window_rows)
  | .window c none above _ => do
    let (a, deps) ← readView (Community.readable c (limit := some above)) #[]
    return (.window (a.rows.map (·.1)).toArray 0, deps)
  | .window c (some p) above below => do
    -- at and older than p (one byte past its id: p itself is in), and newer
    let (o, deps) ← readView (Community.readable c (limit := some above) (before := some (p.1, p.2.push 0))) #[]
    let (n, deps) ← readView (Community.readable c (limit := some below) (desc := false) (after := some p)) deps
    let ids := (n.rows.reverse ++ o.rows).map (·.1)
    return (.window ids.toArray n.rows.length, deps)
  -- counts (limit 0): each watches its key
  | .count c none => do
    let (a, deps) ← readView (Community.readable c (limit := some 0)) #[]
    return (.count 0 a.inRange, deps)
  | .count c (some p) => do
    let (o, deps) ← readView (Community.readable c (limit := some 0) (before := some (p.1, p.2.push 0))) #[]
    let (n, deps) ← readView (Community.readable c (limit := some 0) (after := some p)) deps
    return (.count n.inRange o.inRange, deps)
  | .comms => do
    let (all, deps) ← Kinds.Accepted.read (← get).known
    modify fun s => { s with known := all }
    return (.comms all, deps)
  | .members c user => do
    let (ms, deps) ← Kinds.Profile.members c
    -- an admin: the founder's user (the community's id), or one granted admin
    let (ad, _, deps) ← readList (Community.admin.byUser.query [c, user] (limit := some 0)) deps
    return (.members (ms.map fun (u, ds, p) => (u, ds, p.name)) (!user.isEmpty && (user == c || ad.total > 0)), deps)
  | .asking c => do
    let (rs, deps) ← Kinds.Request.waiting c
    return (.asking rs, deps)
  | .people c => do
    let (ps, deps) ← readView (Kinds.Profile.present c) #[]
    return (.people ps.length, deps)
  | .row c me m => do
    match ← Kinds.Message.read c me m with
    | some (d, deps) => return (.row (some d), deps)
    -- not shown yet: no reads held, so it is read again each pass
    | none => return (.row none, #[])
  | .slices xs => do
    -- each chunk op's read is held: one arriving reads the want again
    let mut raw := #[]
    let mut deps := #[]
    for x in xs do
      match (← get).out.find? (·.op.id == x) with
      | some pd => raw := raw.push pd.op.bytes
      | none =>
        deps := deps.push (Q.op x)
        match ← read (Q.op x) with
        | .bytes (some b) => raw := raw.push b
        | _ => return (.slices none, deps)
    return (.slices (some raw.toList), deps)

/-- Whether w's reads changed: not held, or one of its reads stale
(`Live.staleW`, the model's: engine/renderer/ReaderLaws.lean). -/
def stale (s : St) (w : Want) : Bool :=
  _root_.Live.staleW (fun q => !s.live.fresh q) (fun w => (s.deps[w]?).map (·.toList)) w

/-- w's value, with every read it made recorded whatever it found: a
row not shown yet holds the reads it made, so a notice on one of them,
not every pass, reads it again. -/
def evalLogged (w : Want) : RM Val := do
  modify fun s => { s with log := #[] }
  return (← eval w).1

/-- The index after w's reads move from `old` to `new`. -/
def reindex (rev : Std.HashMap Q (Array Want)) (w : Want) (old new : Array Q) :
    Std.HashMap Q (Array Want) :=
  let rev := old.foldl (fun r q => r.modify q (·.filter (· != w))) rev
  new.foldl (fun r q => r.insert q ((r.getD q #[]).push w)) rev

/-- One pass, in one read transaction; whether it put anything or took
any change. -/
def pass (sh : Shared) (cap : Nat := 64) : RM Bool := do
  let wants ← sh.wants.get
  let gen ← sh.gen.get
  let out ← sh.out.get
  let notes ← sh.notes.modifyGet fun a => (a, #[])
  -- at rest (the writers' counter unmoved, no note, the same wants,
  -- nothing dirty) a pass reads nothing, not even the journal
  -- (RestLaws.start_rest); once a second it reads it anyway, for commits
  -- the counter does not see (the node's purges, until its notify counts
  -- them), and the sessions with it
  let c ← sh.commits.get
  let now ← IO.monoMsNow
  let s0 ← get
  unless _root_.Live.mustRead c s0.seenC (!notes.isEmpty) (gen != s0.gen) s0.dirty (now ≥ s0.readAt + 1000) do
    return false
  modify fun s => { s with seenC := c, readAt := now }
  let rd := (← get).rd
  rd.exec "BEGIN"
  try
    let s ← get
    -- the journal, read first: the commits this pass's reads see
    let (fs, vs, top) ← rd.filingsSince s.seen
    -- the session list, at most every half second, and only in a pass
    -- that opened the store: a session's op is a commit the node's notify
    -- counts, and its purge is seen within the second
    if now ≥ s.peersAt + 500 then
      let all ← ((Connection.allSessions : SqlM SF _)).run rd
      let k := Connection.kept all
      sh.peers.set (all.filterMap fun (cid, p, _) => if k.contains cid then some p else none)
      modify fun s => { s with peersAt := now }
    -- at rest (no filing, no note, the same wants, nothing dirty) a pass
    -- does nothing (RestLaws.rest_idle)
    if fs.isEmpty && vs.isEmpty && notes.isEmpty && gen == s.gen && s.dirty.isEmpty then
      rd.exec "COMMIT"
      return false
    -- the wants moved: the new ones are marked, the gone ones forgotten,
    -- and the reads none of them holds stop being watched (RestLaws.wantIdx;
    -- Screen.screen_subs: what is watched is what the wants read)
    let moved := gen != s.gen
    if moved then
      let want : Std.HashSet Want := wants.foldl (·.insert ·) {}
      let fresh := wants.toList.filter fun w => !s.wantSet.contains w
      let dirty := fresh.foldl (·.insert ·) (s.dirty.filter want.contains)
      let deps := s.deps.filter fun w _ => want.contains w
      let held := deps.fold (fun acc _ qs => qs.foldl (fun a q => a.insert q) acc) ({} : Std.HashSet Q)
      modify fun s => { s with gen, wantSet := want, dirty, deps, last := wants,
                               live := s.live.keep held.contains }
    -- the reads this pass's filings and notes reach (Live.hit, exact per
    -- window), before the notice disarms them; the store's rows and the
    -- outbox's are netted apart: a row the store files as it leaves the
    -- outbox is two changes (stored, no longer pending), not one undone
    let s ← get
    let hit := (s.live.hit fs (vs.map (·.1))).toList ++ (s.live.hit notes #[]).toList
    modify fun s => { s with seen := top, out, live := (s.live.notice fs (vs.map (·.1))).notice notes,
                             passes := s.passes + 1 }
    sh.seen.set top
    -- mark the dirty and the wanted wants those reads name, through the
    -- index, then read the first `cap` marked in the frame's order: the
    -- model's decisions (Live.markHit, Live.pick), so RestLaws'
    -- inv_passIdx and settle_idx are about this pass
    let s ← get
    let marked := (_root_.Live.markHit (fun q => (s.rev.getD q #[]).toList) s.dirty hit).filter
      s.wantSet.contains
    let todo := _root_.Live.pick wants.toList marked cap
    modify fun s => { s with dirty := marked }
    let mut puts : Array (Want × Val) := #[]
    for w in todo do
      let old := (← get).deps.getD w #[]
      let v ← evalLogged w
      modify fun s =>
        { s with deps := s.deps.insert w s.log, dirty := s.dirty.erase w, rev := reindex s.rev w old s.log }
      puts := puts.push (w, v)
    rd.exec "COMMIT"
    if !puts.isEmpty || moved then
      let want := (← get).wantSet
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
