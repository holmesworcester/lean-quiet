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
import ops.app.Lifecycle
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

/-- The frame's wants: the window, its rows, the pictures, the counts,
then the frame's lists. -/
def Want.ofFrame (idsW : Want) (rows pics : Array Want) (countW : Want) (lists : Array Want) : Array Want :=
  #[idsW] ++ rows ++ pics ++ #[countW] ++ lists

/-- The frame's first wants, before it knows its rows: the window and
the counts about the anchor, and the rest as last set. When both are
wanted already, the wants are left as they are, so a steady frame does
not move the generation (`withView_ofFrame`). -/
def Want.withView (ws : Array Want) (idsW countW : Want) : Array Want :=
  if ws.contains idsW && ws.contains countW then ws
  else #[idsW] ++ ws.filter (fun w => w != idsW && w != countW) ++ #[countW]

/-- **A steady frame keeps its wants**: the first set leaves the wants
the last frame set as they were, so with the same anchor, rows and
lists neither set moves the generation and the reader rests. -/
theorem Want.withView_ofFrame (idsW countW : Want) (rows pics lists : Array Want) :
    withView (ofFrame idsW rows pics countW lists) idsW countW = ofFrame idsW rows pics countW lists := by
  simp [withView, ofFrame]

/-- The mutant: the window first and the counts last, every frame. -/
def Want.withViewLast (ws : Array Want) (idsW countW : Want) : Array Want :=
  #[idsW] ++ ws.filter (fun w => w != idsW && w != countW) ++ #[countW]

/-- The mutant moves the wants of every frame with a list: the counts
go last, then back before the lists, so the reader never rests. -/
theorem Want.withViewLast_moves (idsW countW : Want) (rows pics lists : Array Want) (hl : lists ≠ #[])
    (hc : countW ∉ lists) :
    withViewLast (ofFrame idsW rows pics countW lists) idsW countW ≠ ofFrame idsW rows pics countW lists := by
  intro h
  have := congrArg (fun a : Array Want => a.back?) h
  simp [withViewLast, ofFrame, Array.back?_append] at this
  cases hb : lists.back? with
  | none => exact hl (by simpa using hb)
  | some x =>
    rw [hb] at this
    exact hc (this ▸ Array.mem_of_back? hb)

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
  /-- The passes that opened the store. -/
  opens : Nat := 0
  /-- Revocation checked before each query and board publication. -/
  enabled : IO Bool := pure true

abbrev RM := StateT St IO

/-- A user action: its id (the frame's, for its continuation) and its
intent, run in a pass on the reader's connection, before the marks. -/
abbrev Act := Id × RM Community.Write

/-- What the frame and the reader share. -/
structure Shared where
  board : IO.Ref (_root_.Live.Board Want Val)
  /-- The frame's wants, most urgent first. -/
  wants : IO.Ref (Array Want)
  /-- The outbox: the pass's. The frame's own writes join it; the pass
  adds its acts' ops and drops those the store has decided. -/
  out : IO.Ref (Array Pending)
  /-- The rows the frame's own writes filed (to its outbox) since the
  last pass. -/
  notes : IO.Ref (Array Filing)
  /-- The journal's rows the reader has taken (the writer prunes below
  the frame's and this). -/
  seen : IO.Ref Nat
  /-- Moves each time the frame sets `wants` to something new. -/
  gen : IO.Ref Nat
  /-- The writers' commits (the app's writer counts its own, the node's
  notify counts the node's): a pass that sees it unmoved, with no note,
  the same wants and nothing dirty, reads nothing (RestLaws.start_rest). -/
  commits : IO.Ref Nat
  /-- The frame's acts, for the next pass (`Shared.act`). -/
  acts : IO.Ref (Array Act)
  /-- What each act wrote: its write, or none when refused (an op
  Invalid, or the intent failed). The frame takes them, submits each
  write and runs its continuation. -/
  done : IO.Ref (Array (Id × Option Community.Write))

def Shared.new (commits : IO.Ref Nat) : IO Shared :=
  return ⟨← IO.mkRef {}, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0, ← IO.mkRef 0,
    commits, ← IO.mkRef #[], ← IO.mkRef #[]⟩

/-- Queue an act: the next pass opens the store for it (`Live.mustReadActs`). -/
def Shared.act (sh : Shared) (id : Id) (intent : RM Community.Write) : IO Unit :=
  sh.acts.modify (·.push (id, intent))

/-- The frame's wants, set; the generation moves only when they change,
so a reader at rest stays at rest (RestLaws.nextGen_same). -/
def Shared.setWants (sh : Shared) (ws : Array Want) : IO Unit := do
  let old ← sh.wants.get
  sh.gen.modify (_root_.Live.nextGen old ws)
  if old != ws then sh.wants.set ws


/-- A read through the pass's cache (App's `read`, on this connection). -/
def read (q : Q) : RM Ans := do
  let s ← get
  if !(← s.enabled) then return default
  modify fun s => { s with log := s.log.push q }
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

/-- An act's write, judged as App.writeAll judges the frame's: each op
in order against what is decided, the ops before it in the same write,
then the outbox's (pending, so valid), then the store's. Its valid ops,
to show pending; none when one is Invalid (the write is refused). -/
def judgeWrite (rd : Db) (out : Array Pending) (w : Community.Write) : IO (Option (Array Pending)) := do
  let mut mine : Std.HashMap Id (Verdict SF) := {}
  let mut pend := #[]
  for o in w.ops do
    let mut sts := []
    for r in o.reqs do
      sts := sts ++ [← match mine[r]? with
        | some v => pure (some v)
        | none => match out.find? (·.op.id == r) with
          | some p => pure (some (.valid (.inl p.fact)))
          | none => Data.status rd r]
    match judge fam o sts with
    | some (.valid (.inl f)) =>
      mine := mine.insert o.id (.valid (.inl f))
      pend := pend.push (⟨o, f, opKey o.id :: keys f⟩ : Pending)
    | some (.valid v) => mine := mine.insert o.id (.valid v)
    | none => pure ()
    | some .invalid => return none
  return some pend

/-- One pass, in one read transaction; whether it put anything or took
any change. -/
def pass (sh : Shared) (cap : Nat := 64) : RM Bool := do
  if !(← (← get).enabled) then return false
  let wants ← sh.wants.get
  let gen ← sh.gen.get
  let notes ← sh.notes.modifyGet fun a => (a, #[])
  let acts ← sh.acts.modifyGet fun a => (a, #[])
  -- at rest (the writers' counter unmoved, no note, the same wants,
  -- nothing dirty) a pass reads nothing, not even the journal
  -- (RestLaws.start_rest); once a second it reads it anyway, for commits
  -- the counter does not see (the node's purges, until its notify counts
  -- them), and the sessions with it; acts queued open it whatever else
  -- (ActsLaws.acts_force)
  let c ← sh.commits.get
  let now ← IO.monoMsNow
  let s0 ← get
  unless _root_.Live.mustReadActs (!acts.isEmpty) c s0.seenC (!notes.isEmpty) (gen != s0.gen) s0.dirty
      (now ≥ s0.readAt + 1000) do
    return false
  modify fun s => { s with seenC := c, readAt := now, opens := s.opens + 1 }
  let rd := (← get).rd
  rd.exec "BEGIN"
  try
    let s ← get
    -- the journal, read first: the commits this pass's reads see
    let (fs, vs, top) ← rd.filingsSince s.seen
    -- the outbox is the pass's: the ops the store has decided leave it
    -- (their rows move from pending to stored, a notice too)
    let judged : Std.HashSet Id := vs.foldl (fun a (x, _) => a.insert x) {}
    let (out, gone) ← sh.out.modifyGet fun o =>
      let kept := o.filter fun p => !judged.contains p.op.id
      ((kept, o.filter fun p => judged.contains p.op.id), kept)
    modify fun s => { s with out }
    -- the acts, before the marks (ActsLaws.passActs): each intent runs in
    -- this transaction and its write is judged against the store and the
    -- outbox; its valid ops join the outbox, pending, and their rows are
    -- this pass's notices, so the wants they touch are read now
    let mut actNotes : Array Filing := #[]
    for (id, intent) in acts do
      if !(← (← get).enabled) then break
      let r ← try
          let w ← intent
          if !(← (← get).enabled) then pure none
          else pure (some (w, ← judgeWrite rd (← get).out w))
        catch e => do
          IO.eprintln s!"reader: an act failed: {e}"
          pure none
      match r with
      | some (w, some pend) =>
        if !(← (← get).enabled) then break
        modify fun s => { s with out := s.out ++ pend }
        sh.out.modify (· ++ pend)
        actNotes := actNotes ++ Pending.filings pend.toList
        sh.done.modify (·.push (id, some w))
      | _ => sh.done.modify (·.push (id, none))
    let notes := notes ++ Pending.filings gone.toList ++ actNotes
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
    let hitActs := (s.live.hit actNotes #[]).toList
    modify fun s => { s with seen := top, live := (s.live.notice fs (vs.map (·.1))).notice notes,
                             passes := s.passes + 1 }
    sh.seen.set top
    -- mark the dirty and the wanted wants those reads name, through the
    -- index; read every want the acts' rows touched, then the first `cap`
    -- other marked in the frame's order: the model's decisions
    -- (Live.markHit, Live.pickActs), so ActsLaws' acts_shown and
    -- inv_passActs, and with no act RestLaws', are about this pass
    let s ← get
    let rev := fun q => (s.rev.getD q #[]).toList
    let marked := (_root_.Live.markHit rev s.dirty hit).filter s.wantSet.contains
    let touched := (_root_.Live.markHit rev {} hitActs).filter s.wantSet.contains
    let todo := _root_.Live.pickActs wants.toList touched marked cap
    modify fun s => { s with dirty := marked }
    let mut puts : Array (Want × Val) := #[]
    for w in todo do
      let old := (← get).deps.getD w #[]
      let v ← evalLogged w
      modify fun s =>
        { s with deps := s.deps.insert w s.log, dirty := s.dirty.erase w, rev := reindex s.rev w old s.log }
      puts := puts.push (w, v)
    rd.exec "COMMIT"
    if (← (← get).enabled) && (!puts.isEmpty || moved) then
      let want := (← get).wantSet
      sh.board.modify fun b => puts.foldl (fun b (w, v) => b.put w v) (b.keep want.contains)
    return !puts.isEmpty || !fs.isEmpty || !vs.isEmpty || !acts.isEmpty
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
