/-
The connection family end to end: two SQLite nodes (founder A, joiner
B) driven through the engine's node driver, with real Ed25519, X25519
and ChaCha20-Poly1305. A small in-memory wire carries bare frames to an
address and session frames to the other node, and may lose them.

What it checks, in order:
- **Join, before approval:** A opens B's request and stores B's join
  request, and writes no connection back. B establishes nothing. B's
  dial is resent every tick, and A stores the request once.
- **Approval:** after A approves, A answers B's next dial. Both hold one
  established session with the same id and hash, each naming the other,
  with crossed keys; B dialed and A answered.
- **Sync over the session:** B ends admitted by its own ops, lets A in,
  and receives a later post.
- **One session per peer:** after B dials A again, both ends keep the
  same one (the newer dial supersedes), and the other is purged at both.
- **Loss:** with a third of bare (handshake) frames lost, B still
  joins: the dial is resent every tick, and a lost answer is resent when
  the request arrives again. Session frames ride TCP, which loses a
  socket, not a frame inside one; sync under a dying socket is
  holmes-a3's sync tests'.
- **Devices:** one node speaks for every device whose secret it holds.
  A join the device stopped waiting on is not dialed, and the same node
  then joins another community as another device.
- **Purge:** a session that loses the one-per-peer choice is purged
  at both ends.
- **The cache law** (`write_cached`, `purge_cached`): after every phase,
  purges included, each node's room index holds, room by room, exactly
  the index of the ops in its SQLite store (`Index.ofOps` of `dumpOps`).
- **Authenticate before parsing** (`sealed_auth`): a session frame A
  sealed for B, with one byte of its ciphertext or of its header changed,
  leaves B's node and store as they were and sends nothing; the frames
  as sealed are then answered, and B holds the post they offer.

Sessions open by themselves: the node reads the family's `established`
ops and seals every session frame with the session's keys.

Not yet here: the world as a pure step relation to prove laws over
(the node runs on held data already).
-/
import Tests.Lib
import Connection

open Engine Engine.Sync Community Tests Connection

def K := sodium
def fam : Family F := node ed25519 K
def cfg : Config := { every := 30000, patience := 20000 }

structure Peer where
  addr : ByteArray
  seed : ByteArray
  x : Sync F (SqlM F)
  db : Db
  n : Node
  /-- Frames waiting: (the sender's address, bytes). -/
  inbox : List (ByteArray × ByteArray) := []

def mkPeer (name : String) : IO Peer := do
  let seed := sha256 s!"seed {name}".toUTF8
  let addr := s!"{name}:7001".toUTF8
  let db ← Db.openAt ":memory:"
  let x : Sync F (SqlM F) := { fam, cfg, hooks := hooks fam K addr }
  return { addr, seed, x, db, n := Node.boot fam [] 0 }

structure World where
  a : Peer
  b : Peer
  now : Nat := 0
  rng : UInt64 := 0x9E3779B97F4A7C15
  loss : Nat := 0
  sentBare : Nat := 0

def World.rand (w : World) (n : Nat) : Nat × World :=
  let s := w.rng * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, { w with rng := s })

/-- Put one side's effects on the wire to the other. -/
def World.route (w : World) (fromA : Bool) (e : Effects) : World := Id.run do
  let mut w := w
  for (_, bytes) in e.send do
    let (l, w') := w.rand 100
    w := w'
    let bare := bytes[0]? == some 0
    if bare then w := { w with sentBare := w.sentBare + 1 }
    -- Loss on the bare wire (the handshake). Session frames ride TCP,
    -- which loses a socket, not a frame inside it.
    if bare && l < w.loss then continue
    let src := if fromA then w.a.addr else w.b.addr
    if fromA then w := { w with b := { w.b with inbox := w.b.inbox ++ [(src, bytes)] } }
    else w := { w with a := { w.a with inbox := w.a.inbox ++ [(src, bytes)] } }
  return w

def run (p : Peer) (k : Node → SqlM F (Node × Effects)) : IO (Peer × Effects) := do
  let (n, e) ← (k p.n).run p.db
  return ({ p with n }, e)

def deliverAll (p : Peer) (now : Nat) : IO (Peer × Effects) := do
  let mut p := p
  let mut out : Effects := {}
  for (src, bytes) in p.inbox do
    let (p', e) ← run p fun n => n.onFrame p.x src bytes now
    p := p'
    out := { send := out.send ++ e.send, drop := out.drop ++ e.drop, stored := out.stored ++ e.stored }
  return ({ p with inbox := [] }, out)

/-- One step: deliver everything waiting, then tick both. -/
def World.step (w : World) : IO World := do
  let now := w.now + 200
  let (a, ea) ← deliverAll w.a now
  let (b, eb) ← deliverAll w.b now
  let w := ({ w with a, b, now }.route true ea).route false eb
  let (a, ta) ← run w.a fun n => n.onTick w.a.x now
  let (b, tb) ← run w.b fun n => n.onTick w.b.x now
  return ({ w with a, b }.route true ta).route false tb

def World.run (w : World) (steps : Nat) : IO World := do
  let mut w := w
  for _ in [0:steps] do w ← w.step
  return w

def writeA (w : World) (ops : List Op) : IO World := do
  let (a, e) ← run w.a fun n => n.onWrite w.a.x ops w.now
  return { w with a }.route true e

def writeB (w : World) (ops : List Op) : IO World := do
  let (b, e) ← run w.b fun n => n.onWrite w.b.x ops w.now
  return { w with b }.route false e

def cnt (p : Peer) (r : Rel Connection.Fact) (args : List ByteArray) : IO Nat := (count r args : SqlM F _).run p.db
def stored (p : Peer) (x : Id) : IO Bool := do return (← (Store.getOp x : SqlM F _).run p.db).isSome
def ests (p : Peer) : IO (List Connection.Fact) := do
  return (← (rows established.all [] : SqlM F _).run p.db).map (·.2)
def allowedOn (p : Peer) (c d : ByteArray) : IO Bool :=
  ((Community.allowPeer c d).liftL.run : SqlM F Bool).run p.db

/-- A founds Acme and invites at its address; B joins from the link. -/
def setup (loss : Nat) : IO (World × Id × Op) := do
  let a ← mkPeer "A"
  let b ← mkPeer "B"
  let mut w : World := { a, b, loss }
  w ← writeA w (found a.seed "Acme".toUTF8 "Ann".toUTF8 1 (sha256 "key".toUTF8) (sha256 "esk".toUTF8)).ops
  let c := (root (Device.ofSeed a.seed)).id
  let (wi, link) := inviteTo c c a.seed (sha256 "bearer".toUTF8) [a.addr]
  w ← writeA w wi.ops
  w ← writeB w (joinOps link b.seed "Bea".toUTF8).ops
  return (w, c, link.request (Device.ofSeed b.seed))

def approveOnA (w : World) (c : Id) (req : Op) : IO World := do
  let wr ← ((approveReq c req.id c w.a.seed).liftL.run : SqlM F Community.Write).run w.a.db
  writeA w wr.ops

/-- The rooms of a node's index and of its stored ops. -/
def roomsOf (p : Peer) (ops : List Op) : List Id :=
  (p.n.ix.rooms.map (·.1) ++ ops.filterMap fam.room).foldl Engine.ins []

/-- The cache law on SQLite: room by room, the node's index is the index
of the ops its store holds. -/
def cacheOk (p : Peer) : IO Bool := do
  let ops ← (dumpOps (F := F)).run p.db
  let ix := Index.ofOps fam ops
  return (roomsOf p ops).all fun r => decide (p.n.ix.items r = ix.items r)

/-- What a node and its store hold, to compare before and after. -/
def snapshot (p : Peer) : IO (List ByteArray × List (Id × List Item) × List Id × List Id × List Id × Nat) := do
  let ops ← (dumpOps (F := F)).run p.db
  let st ← (dumpStatus (F := F)).run p.db
  return (ops.map (·.bytes), p.n.ix.rooms, p.n.conns.map (·.1), p.n.addrs.map (·.1) ++ p.n.addrs.map (·.2),
    p.n.managed ++ p.n.dropped ++ p.n.fresh, st.length)

def dump (name : String) (p : Peer) : IO Unit := do
  let ops ← (dumpOps (F := F)).run p.db
  let mut line := s!"{name}:"
  for o in ops do
    let st ← (Store.getStatus o.id : SqlM F _).run p.db
    line := line ++ s!" {o.kind}:" ++ (match st with | some (.valid _) => "v" | some .invalid => "X" | none => "?")
  IO.eprintln line

def main : IO UInt32 := do
  let t ← Checks.new
  let (w, c, req) ← setup 0
  let dA := Device.ofSeed w.a.seed
  let dB := Device.ofSeed w.b.seed
  let w ← w.run 20
  -- Before approval.
  if (← IO.getEnv "DUMP").isSome then dump "A" w.a; dump "B" w.b
  t.ok "A opened B's request" ((← cnt w.a opened.all []) == 1)
  t.ok "A stored B's join request" (← stored w.a req.id)
  t.ok "A answered nothing" ((← cnt w.a established.all []) == 0)
  t.ok "B established nothing" ((← ests w.b).isEmpty)
  t.ok "B's dial was resent every tick" (w.sentBare ≥ 15)
  t.ok "B is not admitted on A" (!(← allowedOn w.a c dB.pk))
  -- Approval.
  let w ← approveOnA w c req
  t.ok "A admits B by its own ops" (← allowedOn w.a c dB.pk)
  let w ← w.run 20
  let ea ← ests w.a
  let eb ← ests w.b
  t.ok "each holds one established session" (ea.length == 1 && eb.length == 1)
  let cidOf (es : List Connection.Fact) : ByteArray := match es with
    | [.established i ..] => i
    | _ => .empty
  match ea, eb with
  | [.established ca cca pa ha sa ra da], [.established cb ccb pb hb sb rb db] =>
    t.ok "the same connection id" (ca == cb)
    t.ok "the same community" (cca == c && ccb == c)
    t.ok "each names the other" (pa == dB.pk && pb == dA.pk)
    t.ok "the same handshake hash" (ha == hb)
    t.ok "crossed keys" (sa == rb && ra == sb)
    t.ok "B dialed, A answered" (db && !da)
  | _, _ => t.ok "sessions have the expected shape" false
  -- Sync over the session.
  let w ← w.run 40
  t.ok "B is admitted by its own ops" (← allowedOn w.b c dB.pk)
  t.ok "B lets A in" (← allowedOn w.b c dA.pk)
  let p := post c c dA "k".toUTF8 "hello B".toUTF8 5
  let w ← writeA w [p]
  let w ← w.run 10
  t.ok "a later post reaches B" (← stored w.b p.id)
  t.ok "A's index is the index of its store" (← cacheOk w.a)
  t.ok "B's index is the index of its store" (← cacheOk w.b)
  -- A forged session frame: A seals a post for B; B gets it with one
  -- byte changed, in the ciphertext, and then in the header.
  let p2 := post c c dA "k".toUTF8 "sealed for B".toUTF8 6
  let (a, wa) ← run w.a fun n => n.onWrite w.a.x [p2] w.now
  let w := { w with a }
  let sealed := wa.send.filter fun (_, b) => b[0]? == some 1
  t.ok "A seals the post for B" (!sealed.isEmpty)
  let flip (b : ByteArray) (i : Nat) : ByteArray :=
    ⟨b.data.modify i fun x => x ^^^ 1⟩
  for (_, f) in sealed do
    for i in [f.size - 1, 40, 5] do
      let before ← snapshot w.b
      let (b', e) ← run w.b fun n => n.onFrame w.b.x w.a.addr (flip f i) (w.now + 1)
      t.ok s!"a forged frame (byte {i}) sends nothing" (e.send.isEmpty && e.drop.isEmpty && e.stored.isEmpty)
      t.ok s!"a forged frame (byte {i}) changes neither B's node nor its store"
        ((← snapshot { w.b with n := b'.n }) == before)
  t.ok "the forged frames stored nothing" (!(← stored w.b p2.id))
  -- The frames as sealed offer the post: B asks for it, and holds it
  -- after the exchange.
  let mut wf := w
  let mut answered := false
  for (_, f) in sealed do
    let (b', e) ← run wf.b fun n => n.onFrame wf.b.x wf.a.addr f (wf.now + 1)
    answered := answered || !e.send.isEmpty
    wf := { wf with b := b' }.route false e
  t.ok "the frames as sealed are taken: B answers them" answered
  let w ← wf.run 5
  t.ok "and B then holds the post" (← stored w.b p2.id)
  -- Two sessions between one pair (B dials A again with a fresh
  -- ephemeral): both ends keep the same one, the smaller id.
  let e2 := sha256 "second ephemeral".toUTF8
  let some ro2 := Request.op K w.b.seed dA.pk e2 (hello c w.b.addr []) | t.ok "a second request" false; return 1
  let w ← writeB w [ro2, Eph.op e2 ro2.id, Send.op w.a.addr ro2]
  let w ← w.run 20
  let sa ← (sessions : SqlM F _).run w.a.db
  let sb ← (sessions : SqlM F _).run w.b.db
  t.ok "each end keeps one session with the other" (sa.length == 1 && sb.length == 1)
  t.ok "both keep the same one" (sa.map (·.1) == sb.map (·.1))
  t.ok "the other session was purged at both ends" ((← ests w.a).length == 1 && (← ests w.b).length == 1)
  t.ok "and the kept one is the newer dial" (sa.map (·.1) != [cidOf ea])
  t.ok "after the purge, A's index is the index of its store" (← cacheOk w.a)
  t.ok "after the purge, B's index is the index of its store" (← cacheOk w.b)
  -- Lossy wire.
  let (w2, c2, req2) ← setup 33
  let w2 ← w2.run 30
  let w2 ← approveOnA w2 c2 req2
  let w2 ← w2.run 400
  t.ok "with a third of handshake frames lost, both still establish a session"
    ((← ests w2.a).length ≥ 1 && (← ests w2.b).length ≥ 1)
  if (← IO.getEnv "DUMP").isSome then
    dump "A2" w2.a; dump "B2" w2.b
    IO.eprintln s!"A2 conns {w2.a.n.conns.map (fun p => hex p.1)} dropped {w2.a.n.dropped.map hex}"
    IO.eprintln s!"B2 conns {w2.b.n.conns.map (fun p => hex p.1)} dropped {w2.b.n.dropped.map hex}"
  t.ok "with a third of handshake frames lost, B still joins" (← allowedOn w2.b c2 (Device.ofSeed w2.b.seed).pk)
  t.ok "on the lossy wire, both indexes are their stores'" ((← cacheOk w2.a) && (← cacheOk w2.b))
  -- One node for every device it holds; an abandoned join is not dialed.
  let a3 ← mkPeer "A3"
  let b3 ← mkPeer "B3"
  let mut w3 : World := { a := a3, b := b3 }
  w3 ← writeA w3 (found a3.seed "Acme3".toUTF8 "Ann".toUTF8 1 (sha256 "key3".toUTF8) (sha256 "esk3".toUTF8)).ops
  let c3 := (root (Device.ofSeed a3.seed)).id
  -- A pending join to a community that is not here, as another device.
  let ghost := sha256 "ghost".toUTF8
  let gr := root (Device.ofSeed ghost)
  let (_, deadLink) := inviteTo gr.id gr.id ghost (sha256 "ghost bearer".toUTF8) ["Z:7001".toUTF8]
  let wd := joinOps deadLink (sha256 "old device".toUTF8) "Old".toUTF8
  w3 ← writeB w3 wd.ops
  w3 ← w3.run 5
  t.ok "a pending join is dialed" (w3.sentBare ≥ 3)
  let some jo := wd.ops.getLast? | t.ok "the join's ops" false; return 1
  w3 ← writeB w3 [abandon jo.id]
  let s0 := w3.sentBare
  w3 ← w3.run 10
  t.ok "a join this device stopped waiting on is not dialed" (w3.sentBare == s0)
  -- The same node joins A3 as a second device, with no restart.
  let (wi3, link3) := inviteTo c3 c3 a3.seed (sha256 "bearer3".toUTF8) [a3.addr]
  w3 ← writeA w3 wi3.ops
  w3 ← writeB w3 (joinOps link3 b3.seed "Bea".toUTF8).ops
  w3 ← w3.run 10
  w3 ← approveOnA w3 c3 (link3.request (Device.ofSeed b3.seed))
  w3 ← w3.run 30
  t.ok "the same node then joins as another device" (← allowedOn w3.b c3 (Device.ofSeed b3.seed).pk)
  t.ok "with two devices, both indexes are their stores'" ((← cacheOk w3.a) && (← cacheOk w3.b))
  t.finish "connection_check"
