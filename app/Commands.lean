import engine.wire.Node
import engine.renderer.WriteQueue
import app.community.member.invite.request.Commands
import app.community.member.join.joining.Commands
import app.connection.Commands
import app.connection.Family
import app.connection.connection.Commands
import app.connection.eph.Commands
import app.connection.established.Commands
import app.connection.given.Commands
import app.connection.opened.Commands
import app.connection.recv.Commands
import app.connection.request.Commands
import app.connection.send.Commands
import engine.sync.Notice
import engine.core.Engine
import engine.core.Window
import engine.renderer.Platform
import Std.Data.HashMap
import engine.core.WindowIndex
import app.community.member.invite.request.Op
import app.community.channel.message.reaction.Op
import app.community.Family
import app.community.key.Op
import app.community.key.wrap.Op
import app.community.channel.message.Op
import app.connection.connection.Op
import app.connection.established.Op
import app.community.member.remove.Op
import app.connection.request.Op
import app.connection.recv.Op
import app.community.member.admin.Op
import app.community.member.join.joining.abandon.Op
import app.community.Commands
import app.connection.opened.Op
import app.community.channel.message.attachment.chunk.Op
import app.connection.send.Op
import app.community.channel.message.receipt.Op
import app.community.profile.Op
import app.community.device.secret.Op
import app.community.name.Op
import app.community.member.join.accept.Op
import app.community.member.invite.request.approve.Op
import app.community.channel.message.receipt.Commands
import app.connection.eph.Op
import app.connection.given.Op
import app.community.channel.message.attachment.Op
import app.community.device.endpoint.Op
import app.community.member.invite.Op
import app.community.member.join.joining.Op
import app.community.Op

namespace Connection
open Engine Engine.Sync Codec

/-- The communities this node has accepted, each once: the ones a
session may carry. -/
def heldV : View F (List B) := do
  let a ← View.read (F := F) (Community.accepted.all.query [])
  return (a.lefts.filterMap fun (_, f) => match f with
    | .accepted c _ => some c
    | _ => none).eraseDups

/-- What a connection carries of community c for peer key `peer`: the
room, synced, where this node is a device of c and the trust rule takes
the peer; else a notice of each removal that cuts a device under the
peer's key (`Community.removalsAt`) and is not yet given on it
(`given`); else nothing. -/
def roomFor (given : List Id) (c peer : B) : View F (List Room) := do
  match ← meV c with
  | some me =>
    let ok ← ((trusts c me peer).liftL : View F Bool)
    if ok then return [Room.sync c]
    let xs ← ((Community.removalsAt c peer).liftL : View F (List Id))
    return (xs.filter fun x => !has given x).map (Room.notice c)
  | none => return []

/-- What a connection carries for these (community, peer) pairs. -/
def roomsOf (given : List Id) : List (B × B) → View F (List Room)
  | [] => pure []
  | (c, peer) :: rest => do
    let here ← roomFor given c peer
    let tail ← roomsOf given rest
    return here ++ tail

/-- What connection cid carries now, as a view read afresh on every
step (docs/REMOVAL.md): for each community this node holds and each
peer key cid's established facts name, the room synced, or the notices
owed to a removed member's node, or nothing. A session is one per peer
key, and carries every community both nodes share, whatever its hello
named. A session that carries nothing is retired (`sessions`). -/
def roomsV (cid : Id) : View F (List Room) := do
  let a ← View.read (F := F) (established.byConn.query [cid])
  let given ← givenOn cid
  let cs ← heldV
  roomsOf given ((peersOf a).flatMap fun peer => cs.map (·, peer))
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- This node's keys: each endpoint op's public key, secret and id (one,
the first `found` or `join` writes it). -/
def endpoints : m (List (B × B × Id)) := do
  let a : Answer F ← Lists.list (m := m) (Community.endpoint.all.query [])
  return a.lefts.filterMap fun ((_, x), f) => match f with
    | .endpoint pk sk => some (pk, sk, x)
    | _ => none

/-- deliver: of a hello of community c, the join requests of c not stored
yet. Nothing else of a hello is taken. -/
def joinsOf (fam : Family F) (c : B) : List B → m (List Op)
  | [] => pure []
  | b :: t => do
    let rest ← joinsOf fam c t
    match Op.decode b with
    | none => return rest
    | some o =>
      if joinOf c o && decide (fam.scope o = .shared c) then
        let held ← Store.getOp (m := m) o.id
        return if held.isNone then o :: rest else rest
      else return rest

def deliverAll (fam : Family F) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (_, .opened _ c _ _ hs) :: t => do
    let a ← joinsOf fam c hs
    let b ← deliverAll fam t
    return a ++ b
  | _ :: t => deliverAll fam t

/-- answer: an opened request r of community c from key frm, with no
connection yet, to one of this node's keys, whose initiator the trust
rule takes: an ephemeral, the connection, this side's `established`, and
a courier back to the address the request arrived from. -/
def answerOne (K : Keys) (eps : List (B × B × Id)) (r c frm : B) : m (List Op) := do
  if (← count connection.byRequest [r]) ≠ 0 then return []
  let some ro ← Store.getOp (m := m) r | return []
  let some (.request to _ m1) := (decode ro.body : Option Body) | return []
  let some (_, sk, epOp) := eps.find? (·.1 = to) | return []
  let ok ← ((trusts c to frm).liftL : View F Bool).run
  if !ok then return []
  let some addr ← arrivedFrom r | return []
  let f ← Fresh.fresh
  let some co := Reply.op K r sk frm m1 f | return []
  let eo := Eph.op f co.id
  return [co, eo, Established.op co.id r eo.id epOp, Send.op addr co]

def answerAll (K : Keys) (eps : List (B × B × Id)) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (_, .opened r c frm _ _) :: t => do
    let a ← answerOne K eps r c frm
    let b ← answerAll K eps t
    return a ++ b
  | _ :: t => answerAll K eps t

def react (fam : Family F) (K : Keys) : m (List Op) := do
  let eps ← endpoints
  let opens ← rows opened.all []
  let o1 ← openAll eps
  let o2 ← deliverAll fam opens
  let o3 ← answerAll K eps opens
  let o4 ← establishAll eps
  return o1 ++ o2 ++ o3 ++ o4

/-- What a tick sends for one pending join of community c, by device d,
to the inviter's key at every link hint, if this node is in c as d
(`mine`: a join stopped waiting on is not, nor a cut device's):
- **waiting** (d not admitted here): the request whose hello delivers
  this join's request, resent, or composed if this node holds none,
  until a connection answers it, beside an open session or not (a
  session may be open for other communities, or carry c's old ops after
  a removal: the inviter takes a new device's request only bare);
- **admitted**: the same, while no session to the inviter is open, so a
  dropped session is dialed again. -/
def dialOne (K : Keys) (listen pk sk : B) : Community.Fact → m (List Op)
  | .joining c inviter hints req _ d _ => do
    let some _ := hints.head? | return []
    let some (me, _) ← ((Community.mine c).liftL : View F _).run | return []
    if me ≠ d then return []
    let adm : Answer F ← Lists.list (m := m) (Community.admission.byDevice.query [c, d] (limit := some 0))
    let r? ← requestOf K sk inviter req (← rows request.byFrm [pk])
    let skip ← if adm.total ≠ 0 then connectedTo inviter else
      match r? with
      | some r => do
        let n ← count connection.byRequest [r]
        pure (decide (n ≠ 0))
      | none => pure false
    if skip then return []
    match r? with
    | some r =>
      let ro ← Store.getOp (m := m) r
      return match ro with
        | some ro => hints.map (Send.op · ro)
        | none => []
    | none =>
      let some jr ← Store.getOp (m := m) req | return []
      let e ← Fresh.fresh
      return match Request.op K sk inviter e (hello c listen [jr]) with
        | some ro => [ro, Eph.op e ro.id] ++ hints.map (Send.op · ro)
        | none => []
  | _ => return []

def dialAll (K : Keys) (listen pk sk : B) : List (Pos × Community.Fact) → m (List Op)
  | [] => pure []
  | (_, f) :: rest => do
    let a ← dialOne K listen pk sk f
    let b ← dialAll K listen pk sk rest
    return a ++ b

/-- `listen` is this node's own address, put in its hellos; each pending
join is dialed as `dialOne` says, from this node's key. -/
def dial (K : Keys) (listen : B) (_now : Nat) : m (List Op) := do
  let some (pk, sk, _) := (← endpoints).head? | return []
  let joins : Answer F ← Lists.list (m := m) (Community.joining.all.query [])
  dialAll K listen pk sk joins.lefts

/-- What closing connection cid purges: the connection and the request
it answers. Purge takes every dependent with them: the ephemerals, the
opened and established ops, the couriers and the
arrival records. A connection no longer stored is still named, so
nothing that cites it outlives the close (`close_forgets`). -/
def closing (cid : Id) : m (List Id) := do
  let some co ← Store.getOp (m := m) cid | return [cid]
  return cid :: co.reqs

/-- What connection cid carries now (`roomsV`): rooms synced, and
notices to give. -/
def rooms (cid : Id) : m (List Room) := (roomsV cid).run

/-- Of these sessions, those that carry something (`roomsV`): a room or
a notice not yet given. -/
def carrying : List (Id × B × Bool × B × Nat) → m (List (Id × B × Bool × B × Nat))
  | [] => pure []
  | e :: t => do
    let rs ← (roomsV e.1).run
    let rest ← carrying t
    return if rs.isEmpty then rest else e :: rest

/-- The sessions kept open: one per peer (`kept`), while it carries
something. A session that carries nothing (no room the trust rule takes,
no notice owed) is retired, so a removed member's session closes once
its notices are given (`notice_then_cut`). -/
def openSessions : m (List (Id × B × Bool × B × Nat)) := do
  let all ← allSessions
  let k := kept all
  carrying (all.filter fun e => k.contains e.1)

/-- Open sessions (`openSessions`): id, the bare address the handshake
ran on, and whether this side dialed. -/
def sessions : m (List (Id × B × Bool)) := do
  return (← openSessions).map fun (cid, _, dialer, a, _) => (cid, a, dialer)

/-- Every established session not kept open: to be closed and purged.
Read off the established facts themselves, not `allSessions`, so a
session `sessionOf` cannot place (its handshake's arrival record lost,
as a crash between the two writes of `onFrame` leaves it) is retired
too, rather than holding its keys forever (`retired_complete`). -/
def retired : m (List Id) := do
  let open_ ← openSessions
  return (← rows established.all []).filterMap fun (_, f) => match f with
    | .established cid .. => if open_.any (fun e => decide (e.1 = cid)) then none else some cid
    | _ => none

/-- `retired` as shipped until fs-erase: only the sessions `allSessions`
places, so an established session whose arrival record is missing was
neither kept open nor retired, and its keys and ephemeral stayed in the
store (`shipped_retired_misses`). A negative control: never run. -/
def retiredShipped : m (List Id) := do
  let all ← allSessions
  let open_ ← openSessions
  return all.filterMap fun (cid, _) => if open_.any (fun e => decide (e.1 = cid)) then none else some cid

def outbox : m (List (Id × B × B)) := do
  let mut out := []
  for (x, f) in ← rows send.all [] do
    let .send op addr := f | continue
    let some o ← Store.getOp (m := m) op | continue
    out := (x, addr, o.bytes) :: out
  return out.reverse

/-- Couriers carrying these connections back to `addr`. -/
def resendConns (addr : B) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (cid, _) :: t => do
    let rest ← resendConns addr t
    let co ← Store.getOp (m := m) cid
    return match co with
      | some co => Send.op addr co :: rest
      | none => rest

/-- On every arrival: the first one of an op is recorded, when and how
it came, and a saturated post gets this device's receipt, which orders
it (`Community.receiptFor`). A request that arrives again bare, opened
here for community c from key frm, and still from a peer the trust rule
takes for c, gets its connections resent to where it came from. That is
the healing for a lost answer, as poc-17 has it ("a replayed request is
answered with the identical bytes again"); a removed member's node
replaying its request gets nothing (`resend_trusted`). -/
def onArrival (via : Option Id) (addr : B) (o : Op) (at_ : Nat) : m (List Op) := do
  let n ← count recv.byOp [o.id]
  let first := if n = 0 then [Recv.op o.id via addr at_] else []
  let first := first ++ (← ((Community.receiptFor o).liftL : View F (List Op)).run)
  if via.isSome then return first
  let some (.request to _ _) := (decode o.body : Option Body) | return first
  let some (_, .opened _ c frm _ _) := (← rows opened.byRequest [o.id]).head? | return first
  let ok ← ((trusts c to frm).liftL : View F Bool).run
  if !ok then return first
  let more ← resendConns addr (← rows connection.byRequest [o.id])
  return first ++ more

/-- What the node driver calls. -/
def hooks (fam : Family F) (K : Keys) (listen : B) : Hooks F m where
  rooms := rooms
  onGiven := onGiven
  recv := onArrival
  outbox := outbox
  react := react fam K
  dial := dial K listen
  established := sessions
  closing := closing
  retired := retired
  sealFor := sealFor K
  openFrame := openFrame K
  retryKey := retryKey

end
end Connection

section

/-
The app's data: the engine on SQLite, read and written from two threads.

- **One writer.** A task of its own owns the write connection. It takes
  jobs (ops) from a queue, this node's own
  writes first, and commits each job as one transaction (`receive`).
  Every commit, the writer's or the node's, records each row it files or
  unfiles, with its key and position, in the store's journal
  (Engine.Db.filings), in the same transaction. It also journals the
  app's newest lifecycle checkpoint (`Writer.save`).
- **Reads never wait for it.** The frame reads on its own connection
  (SQLite's WAL: a long write never blocks it), all in one read
  transaction, so a frame is one moment of the store; its notices are the
  journal's rows that moment holds.
- **The frame never writes.** A write on the frame's thread would wait
  for SQLite's write lock while the frame holds its read; a node's
  `wal_checkpoint(TRUNCATE)` (a purge's) holds that lock while it waits
  for every reader to finish: each waits for the other until a busy
  timeout throws.
- **Live answers.** Every read is a query instance (`Q`). Reading one
  arms a one-shot watch on its window (`Q.win`: the part of its key's
  list its answer depends on; a read with a limit, from its last row
  on). A notice is the journal's filings, netted: exactly the instances
  one of whose windows changed go stale (Engine.notice_iff,
  read_notice_iff), and disarm; the next read runs the query again. A
  row filed outside every window on screen (an old message backfilled
  below the newest ones) notices nothing. Between two reads an instance
  is noticed at most once, however much changes, so a sync burst costs
  one read per instance on screen, not one per op.
- **Pending writes.** A write this node composes is judged at once, in
  memory, against decided facts (it may cite only those), and goes into
  the outbox. Every answer includes the outbox's facts, marked pending,
  until the commit that decides them: the same op, the same id.
-/

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

def openDb (path : String) : IO Db := do
  let db ← Db.openAt path
  discard <| (reindexOnce (F := SF) "community-clumps-v1" (fun
    | .inl f => keysOf [message.rootsByKey, message.childrenByKey, received.rootsByKey, received.childrenByKey] f
    | .inr _ => []) (some fam)).run db
  return db

/-! ## The writer -/

structure Writer where
  jobs : IO.Ref WriterQueue
  /-- How many jobs are queued or running. -/
  busy : IO.Ref Nat
  /-- Commit times, µs, for the stats. -/
  commits : IO.Ref (Array (Nat × Nat))
  /-- While set, the writer takes no jobs (a test's or a demo's busy
  writer: what is written meanwhile stays pending). -/
  paused : IO.Ref Bool
  /-- The journal's rows the frames have taken notice of, up to here:
  `prune` deletes them. -/
  read : IO.Ref Nat
  /-- How many commits this writer has made: a reader that sees it
  unmoved (and the node's likewise) need not read the journal. -/
  count : IO.Ref Nat
  /-- The newest checkpoint handed over, numbered, while not yet
  committed (a newer one replaces it). Committed even while `paused`. -/
  saving : IO.Ref (Nat × Option ByteArray)
  /-- The number of the last checkpoint committed. -/
  saved : IO.Ref Nat

/-- Publish pause/resume without losing it to the writer's concurrent snapshot. -/
def Writer.setPaused (w : Writer) (paused : Bool) : IO Unit :=
  w.paused.modify (fun _ => paused)

/-- Publish the joint reader acknowledgement before journal pruning. -/
def Writer.noticed (w : Writer) (seq : Nat) : IO Unit :=
  w.read.modify (fun _ => seq)

def Writer.submit (w : Writer) (j : Job) : IO Unit := do
  if j.ops.isEmpty then return
  w.busy.modify (· + 1)
  w.jobs.modify (·.push j)

/-- Hand a checkpoint to the writer's thread: the frame never commits. -/
def Writer.save (w : Writer) (b : ByteArray) : IO Unit :=
  w.saving.modify fun (n, _) => (n + 1, some b)

/-- Whether the last checkpoint handed over is committed. -/
def Writer.saveDone (w : Writer) : IO Bool :=
  return (← w.saved.get) == (← w.saving.get).1

/-- Attempt the newest checkpoint once before the selected job. An error
retains it for a later turn; a newer generation may replace it meanwhile.
The existing 50 ms error backoff waits only on the writer's thread. -/
def Writer.commitSave (w : Writer) (db : Db) (save : Db → ByteArray → IO Unit) : IO Unit := do
  let (n, some b) ← w.saving.get | return
  try
    save db b
    w.saved.modify (fun _ => n)
    w.saving.modify fun (m, x) => (m, if m == n then none else x)
  catch e =>
    discard <| (IO.eprintln s!"writer: checkpoint: {e}").toBaseIO
    IO.sleep 50

def Writer.run1 (w : Writer) (db : Db) (j : Job) : IO Unit := do
  let t0 ← nowUs
  -- a peer's job keeps only shared ops: a local-only op is this node's
  -- own write, whatever peers send (Engine.Sync: intake_local, stored_local)
  (receive fam (intake fam j.mine j.ops)).run db
  w.count.modify (· + 1)
  let t1 ← nowUs
  w.commits.modify fun cs => (if cs.size > 200 then cs.extract 100 cs.size else cs).push
    (j.ops.length, (t1 - t0).toNat)

/-- One actual writer service turn. Selection, both FIFO queues and phase
move atomically. A failed job retains its busy ownership and rejoins its
class FIFO; only successful service discharges it. Bounds concern completed
selections, not DB time or eventual success of a particular write. -/
def Writer.turn (w : Writer) (db : Db) (save : Db → ByteArray → IO Unit) : IO (Option Job) := do
  let next ← if ← w.paused.get then pure none else
    w.jobs.modifyGet WriterQueue.take
  w.commitSave db save
  match next with
  | none => IO.sleep 2
  | some j =>
    try
      w.run1 db j
      w.busy.modify (· - 1)
    catch e =>
      -- Keep the accepted job owned before any fallible diagnostics. Retry
      -- behind its class's retained work, without counting a new admission.
      w.jobs.modify (·.push j)
      discard <| (IO.eprintln s!"writer: {e}").toBaseIO
      IO.sleep 50
  return next

partial def Writer.loop (w : Writer) (db : Db) (save : Db → ByteArray → IO Unit) : IO Unit := do
  discard <| w.turn db save
  w.loop db save

/-- One actual prune pass, shared by the periodic writer and native tests. -/
def Writer.pruneOnce (w : Writer) (db : Db) : IO Unit := do
  db.pruneFilings (← w.read.get)

/-- Every few seconds, on a connection of its own, delete journal rows
acknowledged by both readers, regardless of which writer committed them. -/
partial def Writer.prune (w : Writer) (db : Db) : IO Unit := do
  IO.sleep 5000
  try w.pruneOnce db
  catch e => IO.eprintln s!"journal prune: {e}"
  w.prune db

/-- The journal of keys alone, as stores before positions kept it: its
triggers would fill it for ever, nothing pruning it. -/
def dropKeyJournal (db : Db) : IO Unit := db.exec "
DROP TRIGGER IF EXISTS journal_idx;
DROP TRIGGER IF EXISTS journal_status;
DROP TRIGGER IF EXISTS journal_unidx;
DROP TRIGGER IF EXISTS journal_unstatus;
DROP TABLE IF EXISTS changes;
"

/-- `save` commits a checkpoint handed over (`Writer.save`). -/
def Writer.start (path : String) (save : Db → ByteArray → IO Unit) : IO Writer := do
  let db ← openDb path
  -- every commit, this writer's or the node's, records the rows it files
  -- and unfiles in the store's journal (Db.filings), where frames and the
  -- reader take their notices
  dropKeyJournal db
  db.filings
  let w : Writer := ⟨← IO.mkRef WriterQueue.empty, ← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef false, ← IO.mkRef 0, ← IO.mkRef 0,
    ← IO.mkRef (0, none), ← IO.mkRef 0⟩
  let _ ← IO.asTask (prio := .dedicated) (w.loop db save)
  let _ ← IO.asTask (prio := .dedicated) (w.prune (← openDb path))
  return w

/-! ## Queries and answers

Every read is a list (Engine.Query): one fact is the list under its own
id's key (`factQ`), so a component's subscriptions are exactly the
windows of the lists it reads (Engine.read_rows_iff: a read's rows
change exactly when its window's do). The one other read is an op's own
bytes (a chunk's slice, a pending request's body), immutable, watched on
the op's verdict. -/

inductive Q where
  | list (q : ListQ)
  /-- An op as stored, whatever its verdict (this device's own undecided
  request, say): its bytes. -/
  | op (x : Id)
  deriving BEq, Hashable, Inhabited

/-- One fact: the list under its op's own key, at most one row (what
`readFact` reads). -/
def factQ (x : Id) : ListQ := { key := opKey x, limit := some 1 }

/-- What a read answers; `pending` names rows from the outbox. -/
inductive Ans where
  | list (a : Answer Fact) (pending : List Id)
  | bytes (b : Option ByteArray)
  deriving Inhabited, BEq

/-- The key an op's verdict is journaled under, for reads of its bytes:
apart from every list's key (0xFE leads it). -/
def verdictKey (x : Id) : ByteArray := ⟨#[0xFE] ++ x.data⟩

/-- **The window q's answer a depends on**: a list read's watch
(`ListQ.watch`: a count's whole key, a counted read's range, else its
rows' window, cut at its last row); an op's bytes', its verdict. Reads of
an op's bytes are outside the exact laws: their value changes when the
op is stored, which files nothing, so they are noticed per verdict, as
before. -/
def Q.win : Q → Ans → Win
  | .list q, .list a _ => q.watch a
  | .list q, _ => Win.all q.key
  | .op x, _ => Win.all (verdictKey x)

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
  -- Pending flags describe returned rows only. Keeping an out-of-window
  -- id here would let its commit change the answer outside its watch.
  let pending := mine.filter (fun p => rows.any (·.1.2 == p.op.id))
  return (⟨rows, a.inRange + inR.length, a.total + mine.length⟩, pending.map (·.op.id))

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
and the windows of those fresh, indexed (Engine.Subs): each armed once. -/
structure Live where
  entries : Std.HashMap Q Entry := {}
  subs : Subs Q := {}
  reads : Nat := 0
  deriving Inhabited

/-- Instance q goes stale. -/
def Live.staleOne (l : Live) (q : Q) : Live :=
  match l.entries[q]? with
  | some e => { l with entries := l.entries.insert q { e with stale := true } }
  | none => l

/-- The instances a batch reaches: its filings netted and matched against
the windows (Engine.Subs.notify); and the reads of the bytes of each op
whose verdict was recorded or cleared (not netted: a verdict recorded and
cleared in one batch may still have taken the bytes). -/
def Live.hit (l : Live) (fs : Array Filing) (vs : Array Id) : Std.HashSet Q :=
  let xs := l.subs.notify fs ++ _root_.Id.run (l.subs.notifyM (vs.toList.map fun x => (verdictKey x, (.empty, x))))
  xs.foldl (·.insert ·) {}

/-- **A notice**: the journal's filings (and the outbox's), and its
verdicts. Exactly the instances one of whose windows changed go stale,
and disarm. -/
def Live.notice (l : Live) (fs : Array Filing) (vs : Array Id := #[]) : Live :=
  let hit := l.hit fs vs
  if hit.isEmpty then l else
  { hit.fold Live.staleOne l with subs := l.subs.keep fun q => !hit.contains q }

/-- q's answer, if no notice has made it stale: what a read returns
without asking the store. -/
def Live.answer (l : Live) (q : Q) : Option Ans := match l.entries[q]? with
  | some e => if e.stale then none else some e.ans
  | none => none

/-- Whether q has an answer that no notice has made stale. -/
def Live.fresh (l : Live) (q : Q) : Bool := match l.entries[q]? with
  | some e => !e.stale
  | none => false

/-- Record q's answer just read, and arm its window (once: a window it
still held goes). -/
def Live.store (l : Live) (q : Q) (a : Ans) : Live :=
  let subs := if l.fresh q then l.subs.keep (· != q) else l.subs
  { l with
    entries := l.entries.insert q ⟨a, false⟩
    subs := subs.add q (q.win a)
    reads := l.reads + 1 }

/-- A read through the cache: its answer if no notice has made it stale,
else `run`'s (the store's), recorded. Reader.read uses this function
(LiveLaws.read_one_moment is about it). -/
def Live.readWith {m : Type → Type} [Monad m] (run : Q → m Ans) (q : Q) : StateT Live m Ans := do
  if let some a := (← get).answer q then return a
  let a ← run q
  modify (·.store q a)
  return a

/-- Forget instances nobody reads any more, and their windows. -/
def Live.keep (l : Live) (want : Q → Bool) : Live :=
  { l with entries := l.entries.filter fun q _ => want q, subs := l.subs.keep want }

/-- The outbox's own notice: its ops' rows, as the store will file them,
coming (or, once the store holds them, going from the outbox). -/
def Pending.filings (ps : List Pending) : Array Filing :=
  (ps.flatMap fun p => p.keys.map fun k => (⟨k, p.pos, true⟩ : Filing)).toArray

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
    -- only what the read's watch covers: the counts its reader uses
    -- (ListQ.kept, Q.win)
    return .list (q.kept a) pend
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
  let (a, pend, deps) ← readList (factQ x) deps
  return (a.rows.head?.map (·.2), pend.contains x, deps)

/-- The set operation actually used by list-backed component views. -/
def projectSet {α : Type} [BEq α] (rows : List (Pos × Fact)) (project : Fact → Option α) : List α :=
  (rows.filterMap fun (_, f) => project f).eraseDups

theorem projectSet_mem {α : Type} [BEq α] [LawfulBEq α]
    (rows : List (Pos × Fact)) (project : Fact → Option α) (x : α) :
    x ∈ projectSet rows project ↔ ∃ row ∈ rows, project row.2 = some x := by
  simp [projectSet, List.mem_eraseDups, List.mem_filterMap]

private theorem set_nodup {α : Type} [BEq α] [LawfulBEq α] : ∀ xs : List α, xs.eraseDups.Nodup
  | [] => by simp
  | x :: xs => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨?_, set_nodup _⟩
    rw [List.mem_eraseDups]
    simp
termination_by xs => xs.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _))

theorem projectSet_nodup {α : Type} [BEq α] [LawfulBEq α]
    (rows : List (Pos × Fact)) (project : Fact → Option α) :
    (projectSet rows project).Nodup := set_nodup _

/-- A set projected from a list, in first-occurrence order. The same
query/watch/outbox path serves lists, sets, cardinality and membership.
The projection is a view operation, not a second storage API. -/
def readSet {α : Type} [BEq α] (q : ListQ) (project : Fact → Option α)
    (deps : Array Q) : m (List α × Array Q) := do
  let (a, _, deps) ← readList q deps
  return (projectSet a.rows project, deps)

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

end

section

/-
One moment: the live answers a frame reads are all of one state of the
store, over the running cache (Live.answer, Live.store, Live.notice,
Live.keep).

A frame runs in one read transaction (App's `step`). Two things are
assumed of SQLite, and only these:

- **snapshot**: inside one read transaction, every read answers as one
  state of the store (SQLite's snapshot isolation, a WAL reader); a
  moment `ans : Q → Ans` is those answers (with the outbox);
- **journal**: the rows and verdicts the journal hands a frame
  (`takeChanges`, the frame's first read), netted and matched against
  the windows the cache watches (`Live.hit`), reach every instance whose
  answer changed since the last moment. Over the engine's model this is
  a theorem for a read of rows: its rows change exactly when its window
  does (Engine.read_notice_iff, for a batch of commits and purges);
  SQLite's triggers are tested against it (tests/engine/WindowCheck.lean).

From them: `Agrees l ans`, that every answer the cache holds unstaled is
the moment's and its window is watched (in an index kept well formed),
holds from the empty cache (`agrees_empty`), through a read that asks
the store (`agrees_store`), a notice of the journal's rows
(`agrees_notice`, moving to the next moment) and a pruning
(`agrees_keep`); and a read the cache answers returns the moment's
answer (`answer_agrees`). So every answer a frame reads, cached or not,
is of the frame's one moment (`read_one_moment`): no part of the screen
is newer than another. And the cache watches nothing it does not hold:
every window it watches is a fresh answer's (`watched_held`), so no
notice reaches a read the frame has dropped.
-/

namespace LiveLaws
open Engine Data

theorem byteArray_lawful : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

attribute [local instance] byteArray_lawful

theorem listQ_lawful : LawfulBEq ListQ where
  eq_of_beq {a b} h := by
    cases a; cases b
    unfold BEq.beq instBEqListQ at h
    dsimp only at h
    unfold instBEqListQ.beq at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  rfl {a} := by
    cases a
    unfold BEq.beq instBEqListQ
    dsimp only
    unfold instBEqListQ.beq
    simp

attribute [local instance] listQ_lawful

theorem q_lawful : LawfulBEq Q where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> unfold BEq.beq instBEqQ at h <;> dsimp only at h <;> unfold instBEqQ.beq at h
    all_goals simp_all
  rfl {a} := by
    cases a <;> unfold BEq.beq instBEqQ <;> dsimp only <;> unfold instBEqQ.beq <;> simp

attribute [local instance] q_lawful

/-- **The cache agrees with moment `ans`:** its index is well formed, and
every answer it holds that no notice has made stale is the moment's, and
its window is watched (so a notice of a row in it reaches it). -/
def Agrees (l : Live) (ans : Q → Ans) : Prop :=
  l.subs.WF ∧ ∀ q e, l.entries[q]? = some e → e.stale = false →
    e.ans = ans q ∧ l.subs.Has q (q.win e.ans)

theorem agrees_empty (ans : Q → Ans) : Agrees {} ans :=
  ⟨Subs.wf_empty, fun q e he => by simp at he⟩

/-- **A read the cache answers is the moment's.** -/
theorem answer_agrees {l : Live} {ans : Q → Ans} {q : Q} {a : Ans} (h : Agrees l ans)
    (ha : l.answer q = some a) : a = ans q := by
  unfold Live.answer at ha
  split at ha
  · next e he =>
    split at ha
    · cases ha
    · next hs => simp only [Option.some.injEq] at ha; subst ha; exact (h.2 q e he (by simpa using hs)).1
  · cases ha

/-- **A read that asks the store keeps the cache in agreement**, when
the store answers as the moment (snapshot). -/
theorem agrees_store {l : Live} {ans : Q → Ans} (h : Agrees l ans) (q : Q) :
    Agrees (l.store q (ans q)) ans := by
  have hk : (if l.fresh q then l.subs.keep (· != q) else l.subs).WF := by
    split
    · exact Subs.keep_wf h.1 _
    · exact h.1
  refine ⟨Subs.add_wf hk _ _, fun q' e he hs => ?_⟩
  simp only [Live.store, Std.HashMap.getElem?_insert, beq_iff_eq] at he ⊢
  by_cases hq : q = q'
  · subst hq
    rw [if_pos (beq_self_eq_true q), Option.some.injEq] at he
    subst he
    exact ⟨rfl, (Subs.has_add _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩
  · rw [if_neg (fun hb => hq (eq_of_beq hb))] at he
    obtain ⟨hans, hw⟩ := h.2 q' e he hs
    refine ⟨hans, (Subs.has_add _ _ _ _).2 (Or.inl ?_)⟩
    split
    · exact (Subs.has_keep _ _ _).2 ⟨hw, by simpa using Ne.symm hq⟩
    · exact hw

/-! ## Notices -/

theorem staleAll_entries (qs : List Q) : ∀ (l : Live) {q : Q} {e : Entry},
    (qs.foldl Live.staleOne l).entries[q]? = some e → e.stale = false →
      l.entries[q]? = some e ∧ q ∉ qs := by
  induction qs with
  | nil => intro l q e he _; exact ⟨he, by simp⟩
  | cons q0 t ih =>
    intro l q e he hs
    obtain ⟨h1, hn⟩ := ih (l.staleOne q0) he hs
    unfold Live.staleOne at h1
    split at h1
    · next e0 h0 =>
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at h1
      by_cases hq : q0 = q
      · subst hq; rw [if_pos (beq_self_eq_true q0), Option.some.injEq] at h1; subst h1; simp at hs
      · rw [if_neg (fun hb => hq (eq_of_beq hb))] at h1
        exact ⟨h1, by simp [Ne.symm hq, hn]⟩
    · next h0 =>
      refine ⟨h1, ?_⟩
      intro hm
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [h0] at h1; cases h1
      · exact hn hm

/-- **A notice of the journal's rows moves the cache to the next
moment.** If every instance whose answer changed from `ans` to `ans'` is
one the rows reach (journal), the cache after the notice agrees with
`ans'`. -/
theorem agrees_notice {l : Live} {ans ans' : Q → Ans} (h : Agrees l ans) (fs : Array Filing) (vs : Array Id)
    (hj : ∀ q, (l.hit fs vs).contains q = false → ans' q = ans q) : Agrees (l.notice fs vs) ans' := by
  unfold Live.notice
  simp only
  generalize l.hit fs vs = hit at hj ⊢
  split
  · next hem =>
    refine ⟨h.1, fun q e he hs => ?_⟩
    obtain ⟨hans, hw⟩ := h.2 q e he hs
    have : hit.contains q = false := by
      cases hc : hit.contains q
      · rfl
      · exact absurd (Std.HashSet.contains_iff_mem.1 hc) ((Std.HashSet.isEmpty_iff_forall_not_mem.1 hem) q)
    exact ⟨hans.trans (hj q this).symm, hw⟩
  · constructor
    · show (l.subs.keep fun q => !hit.contains q).WF
      exact Subs.keep_wf h.1 _
    · intro q e he hs
      change (Std.HashSet.fold Live.staleOne l hit).entries[q]? = some e at he
      show e.ans = ans' q ∧ (l.subs.keep fun q => !hit.contains q).Has q (q.win e.ans)
      rw [Std.HashSet.fold_eq_foldl_toList] at he
      obtain ⟨h1, hn⟩ := staleAll_entries _ l he hs
      have hc : hit.contains q = false := by
        cases hc : hit.contains q
        · rfl
        · exact absurd (Std.HashSet.mem_toList.2 (Std.HashSet.contains_iff_mem.1 hc)) hn
      obtain ⟨hans, hw⟩ := h.2 q e h1 hs
      exact ⟨hans.trans (hj q hc).symm, (Subs.has_keep _ _ _).2 ⟨hw, by simp [hc]⟩⟩

/-- **Forgetting instances keeps the rest in agreement.** -/
theorem agrees_keep {l : Live} {ans : Q → Ans} (h : Agrees l ans) (want : Q → Bool) :
    Agrees (l.keep want) ans := by
  refine ⟨Subs.keep_wf h.1 want, fun q e he hs => ?_⟩
  simp only [Live.keep, Std.HashMap.getElem?_filter, Std.HashMap.getKey_eq] at he ⊢
  simp only [Option.pfilter_eq_some_iff] at he
  obtain ⟨he1, hw⟩ := he
  obtain ⟨hans, hh⟩ := h.2 q e he1 hs
  exact ⟨hans, (Subs.has_keep _ _ _).2 ⟨hh, hw⟩⟩

/-- **Unmounting keeps the cache in agreement.** A component unmounts:
the reads it alone made (`qs`) are forgotten, and their windows are no
longer watched; every other answer the cache holds is still the
moment's, and watched. -/
theorem agrees_unmount {l : Live} {ans : Q → Ans} (h : Agrees l ans) (qs : Std.HashSet Q) :
    Agrees (l.keep fun q => !qs.contains q) ans ∧
      ∀ q, qs.contains q = true → ∀ w, ¬ (l.keep fun q => !qs.contains q).subs.Has q w := by
  refine ⟨agrees_keep h _, fun q hq w hw => ?_⟩
  have h2 : (!qs.contains q) = true := ((Subs.has_keep (I := l.subs) (fun q => !qs.contains q) q w).1 hw).2
  rw [hq] at h2
  cases h2

/-- **What the cache watches, it keeps:** after forgetting the instances
nobody wants, no window of one is watched (so no notice reaches a read
the frame dropped: Screen.screen_subs on the cache). -/
theorem watched_held {l : Live} (want : Q → Bool) {q : Q} {w : Win} (hw : (l.keep want).subs.Has q w) :
    want q = true := ((Subs.has_keep _ _ _).1 hw).2

/-- **One moment.** A read through the cache (`Live.readWith`, which
App's `read` and the reader's run) whose cache agrees with the moment,
and whose store answers as it (snapshot), returns the moment's answer,
cached or not, and leaves the cache in agreement. -/
theorem read_one_moment {l : Live} {ans : Q → Ans} (h : Agrees l ans) (q : Q) :
    let r := (Live.readWith (m := Id) (fun q => pure (ans q)) q).run l
    r.1 = ans q ∧ Agrees r.2 ans := by
  simp only [Live.readWith, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure]
  cases ha : l.answer q with
  | some a => exact ⟨answer_agrees h ha, h⟩
  | none =>
    simp only [modify, modifyGet, MonadStateOf.modifyGet]
    exact ⟨rfl, agrees_store h q⟩

end LiveLaws

end
