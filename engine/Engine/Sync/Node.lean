/-
A node's sync: its store, its room index and its open connections, with
the entry points a daemon calls (bytes from a session or from the bare
wire, the clock, local writes), so the daemon is sockets, timers and
discovery only. It holds no protocol: which rooms a connection's peer
may see, what a room's first settle writes, how an arrival is recorded,
and what the Connection family wants sent come from that family
(`Hooks`).

- Every write goes through `put`: one write turn through an intake,
  then the index grows by what was stored, and the stored ids are
  offered on every connection whose peer may see them (refreshing each
  connection's rooms first: an admission or a removal changes them).
- The bare wire takes conn ops only (`intakeConn`): the handshake.
- Sessions come from the family: after each entry point, every
  connection its handshake has established is opened here (with its
  `Sealer`, kept in memory), and every one it no longer lists is closed
  and reported in `drop`; the runner binds the handshake's socket to
  the session (`bind`).
- Frames on a session are sealed and unsealed here; one that does not
  unseal drops the session. The bare wire is not sealed: it carries
  only the handshake's ops.
- After each entry point the family's outbox (its `send` couriers) is
  handed out once and marked shipped. Sync's own round messages go out
  directly: they are transient and never stored.
- Every id stored is reported (`stored`), so an app can re-read.
-/
import Engine.Sync.Conn
import Engine.Sqlite

namespace Engine.Sync

/-- Where bytes go: a session, or an address on the bare wire. -/
inductive Route where
  | conn (cid : Id)
  | bare (addr : ByteArray)
  deriving Inhabited

/-- A session's sealing: its state (keys, nonces), sealing a payload
into a frame and unsealing a frame into a payload, each returning the
next state. -/
structure Sealer where
  state : ByteArray
  sealFrame : ByteArray → ByteArray → ByteArray × ByteArray
  openFrame : ByteArray → ByteArray → Option (ByteArray × ByteArray)

/-- No sealing: for the in-memory harness only. -/
def Sealer.plain : Sealer := ⟨.empty, fun s b => (s, b), fun s b => some (s, b)⟩

/-- What the Connection family tells sync. -/
structure Hooks (F : Type) where
  /-- The rooms the peer on connection cid may see now. -/
  rooms : Id → SqlM F (List Id)
  /-- The local ops that record room r's first settle on connection cid. -/
  settled : Id → Id → List Op := fun _ _ => []
  /-- What the family writes on op o's arrival (on a session, or bare
  from an address) at a time: called on every arrival, an op sent again
  included, after it is stored. Recording the first arrival, and
  answering a replayed request again, are the family's. -/
  recv : Option Id → ByteArray → Op → Nat → SqlM F (List Op) := fun _ _ _ _ => pure []
  /-- The family's send couriers waiting: id, route, bytes. -/
  outbox : SqlM F (List (Id × Route × ByteArray)) := pure []
  /-- The local ops that mark a courier handed out. -/
  shipped : Id → List Op := fun _ => []
  /-- What the family writes in answer to what is stored (views over
  lists, returning ops): run after every write, to a fixpoint. -/
  react : SqlM F (List Op) := pure []
  /-- What the family writes as time passes (dialing, retries). -/
  dial : Nat → SqlM F (List Op) := fun _ => pure []
  /-- The sessions established and not closed: connection id, the bare
  address its handshake ran on, and whether this side dialed. -/
  established : SqlM F (List (Id × ByteArray × Bool)) := pure []
  /-- A session's sealer, once its keys are known. -/
  session : Id → SqlM F (Option Sealer) := fun _ => pure none

/-- A node's sync setup: its family, the connection settings, and the
Connection family's hooks. -/
structure Sync (F : Type) where
  fam : Family F
  cfg : Config := {}
  hooks : Hooks F

structure Node where
  db : Db
  ix : Index
  floor : Nat
  conns : List (Id × Conn) := []
  /-- Each open session's sealer. -/
  seals : List (Id × Sealer) := []
  /-- The sessions opened from the family's `established`. -/
  managed : List Id := []
  /-- Ids stored since the last entry point returned. -/
  fresh : List Id := []
  /-- Sessions dropped here: never reopened (a session's keys are its
  handshake's; a new connection needs a new handshake). -/
  dropped : List Id := []

/-- What to do: bytes to send, connections to drop, sockets to bind to
sessions (session, the bare address its handshake ran on), ids stored. -/
structure Effects where
  send : List (Route × ByteArray) := []
  drop : List Id := []
  bind : List (Id × ByteArray) := []
  stored : List Id := []

instance : Append Effects :=
  ⟨fun a b => ⟨a.send ++ b.send, a.drop ++ b.drop, a.bind ++ b.bind, a.stored ++ b.stored⟩⟩

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F)

def Node.boot (db : Db) (floor : Nat) : IO Node := do
  let ops ← (dumpOps (F := F)).run db
  return { db, ix := Index.ofOps x.fam ops, floor }

def Node.conn? (n : Node) (cid : Id) : Option Conn :=
  (n.conns.find? fun p => Decidable.decide (p.1 = cid)).map (·.2)

def Node.close (n : Node) (cid : Id) : Node :=
  { n with
    conns := n.conns.filter fun p => !Decidable.decide (p.1 = cid)
    seals := n.seals.filter fun p => !Decidable.decide (p.1 = cid)
    managed := n.managed.filter fun c => !Decidable.decide (c = cid) }

/-- A session ends here (patience, a frame that does not unseal, its
socket closed): closed, and never reopened. -/
def Node.drop (n : Node) (cid : Id) : Node :=
  let n := n.close cid
  { n with dropped := if has n.dropped cid then n.dropped else cid :: n.dropped }

def Node.sealer? (n : Node) (cid : Id) : Option Sealer :=
  (n.seals.find? fun p => Decidable.decide (p.1 = cid)).map (·.2)

def Node.setSealer (n : Node) (cid : Id) (s : Sealer) : Node :=
  { n with seals := n.seals.map fun p => if p.1 = cid then (cid, s) else p }

def sends (cid : Id) (ops : List Op) : Effects := { send := ops.map fun o => (.conn cid, o.bytes) }

/-- One write turn of ops already through an intake, of those not
already stored; the index grows by them; the ids newly stored. An op
sent again is neither written nor reported again. -/
def Node.write (n : Node) (ops : List Op) : IO (Node × List Id) := do
  let mut absent : List Op := []
  for o in ops do
    if !absent.any (·.id == o.id) then
      if (← (Store.getOp (F := F) o.id : SqlM F _).run n.db).isNone then absent := o :: absent
  if absent.isEmpty then return (n, [])
  let news := absent.reverse
  (receive x.fam news).run n.db
  let mut ix := n.ix
  let mut ids : List Id := []
  for o in news do
    if (← (Store.getOp (F := F) o.id : SqlM F _).run n.db).isSome then
      ix := ix.add x.fam o
      ids := o.id :: ids
  return ({ n with ix, fresh := n.fresh ++ ids.reverse }, ids.reverse)

/-- One write turn through `intake`. -/
def Node.put (n : Node) (ops : List Op) (mine : Bool) : IO (Node × List Id) :=
  n.write x (intake x.fam mine ops)

/-- Write each settle the steps report. -/
def Node.settle (n : Node) (st : List (Id × Status)) : IO Node := do
  let ops := st.flatMap fun (cid, .settled r) => x.hooks.settled cid r
  return (← n.put x ops true).1

/-- Offer stored ids on every connection, with its rooms refreshed. -/
def Node.fanout (n : Node) (ids : List Id) : IO (Node × Effects) := do
  let mut conns : List (Id × Conn) := []
  let mut out : Effects := {}
  let mut st : List (Id × Status) := []
  for (cid, c) in n.conns do
    let c := c.setRooms (← (x.hooks.rooms cid).run n.db)
    let s ← (Conn.filed x.fam x.cfg c ids : SqlM F Step).run n.db
    conns := (cid, s.conn) :: conns
    out := out ++ sends cid s.send
    st := st ++ s.status.map (cid, ·)
  let n ← Node.settle x { n with conns := conns.reverse } st
  return (n, out)

/-- Store ops (a local write, or a peer's) and offer them on; then
write what the family answers, until it answers nothing (at most
`react` rounds). -/
def Node.store (n : Node) (ops : List Op) (mine : Bool) : IO (Node × Effects) := do
  let (n, ids) ← n.put x ops mine
  if ids.isEmpty then return (n, {})
  let (n, out) ← n.fanout x ids
  let mut n := n
  let mut out := out
  for _ in [0:16] do
    let more ← x.hooks.react.run n.db
    if more.isEmpty then break
    let (n', ids) ← n.put x more true
    if ids.isEmpty then break
    let (n'', o) ← n'.fanout x ids
    n := n''
    out := out ++ o
  return (n, out)

/-- Hand out the family's outbox once, and mark it shipped. -/
def Node.flush (n : Node) (out : Effects) : IO (Node × Effects) := do
  let box ← x.hooks.outbox.run n.db
  if box.isEmpty then return (n, out)
  let (n, _) ← n.put x (box.flatMap fun (i, _) => x.hooks.shipped i) true
  return (n, out ++ { send := box.map fun (_, r, b) => (r, b) })

/-- Open a session's connection: say hello. -/
def Node.open (n : Node) (cid : Id) (dialer : Bool) (sealer : Sealer) (now : Nat) :
    IO (Node × Effects) := do
  let s := Conn.open dialer (← (x.hooks.rooms cid).run n.db) n.floor now
  let n := n.close cid
  return ({ n with conns := (cid, s.conn) :: n.conns, seals := (cid, sealer) :: n.seals },
    sends cid s.send)

/-- Follow the family's sessions: open the newly established, close the
ones it no longer lists. -/
def Node.follow (n : Node) (now : Nat) : IO (Node × Effects) := do
  let est ← x.hooks.established.run n.db
  let mut n := n
  let mut out : Effects := {}
  for cid in n.managed do
    if !est.any (fun e => Decidable.decide (e.1 = cid)) then
      n := n.close cid
      out := out ++ { drop := [cid] }
  for (cid, addr, dialer) in est do
    if !has n.managed cid && !has n.dropped cid then
      if let some sealer ← (x.hooks.session cid).run n.db then
        let (n', o) ← n.open x cid dialer sealer now
        n := { n' with managed := cid :: n'.managed }
        out := out ++ { bind := [(cid, addr)] } ++ o
  return (n, out)

/-- Seal what goes on sessions, in order; a send on a session that is
not open is dropped. -/
def Node.sealAll (n : Node) (out : Effects) : Node × Effects := Id.run do
  let mut n := n
  let mut sent : List (Route × ByteArray) := []
  for (r, b) in out.send do
    match r with
    | .bare _ => sent := (r, b) :: sent
    | .conn cid =>
      match n.sealer? cid with
      | none => pure ()
      | some s =>
        let (st, f) := s.sealFrame s.state b
        n := n.setSealer cid { s with state := st }
        sent := (r, f) :: sent
  return (n, { out with send := sent.reverse })

/-- Every entry point ends here: follow the sessions, hand out the
outbox, seal, and report what was stored. -/
def Node.finish (n : Node) (out : Effects) (now : Nat) : IO (Node × Effects) := do
  let (n, o) ← n.follow x now
  -- The handshake's bare replies go before a new session's first frame.
  let (n, out) ← n.flush x out
  let out := out ++ o
  let (n, out) := n.sealAll out
  return ({ n with fresh := [] }, { out with stored := out.stored ++ n.fresh })

/-- Apply a connection's step. -/
def Node.apply (n : Node) (cid : Id) (s : Step) (now : Nat) : IO (Node × Effects) := do
  if s.drop then return (n.drop cid, { drop := [cid] })
  let n := { n with conns := n.conns.map fun p => if p.1 = cid then (cid, s.conn) else p }
  let n ← Node.settle x n (s.status.map (cid, ·))
  let (n, out) ← n.store x s.take false
  let mut arrived : List Op := []
  for o in s.take do
    arrived := arrived ++ (← (x.hooks.recv (some cid) .empty o now).run n.db)
  let (n, out') ← n.store x arrived true
  return (n, sends cid s.send ++ out ++ out')

/-- A connection opened without a handshake, unsealed: the in-memory
harness's. -/
def Node.connect (n : Node) (cid : Id) (dialer : Bool) (now : Nat) : IO (Node × Effects) := do
  let (n, out) ← n.open x cid dialer Sealer.plain now
  n.finish x out now

/-- A frame on session cid: unsealed, then the connection's; one that
does not unseal drops the session. -/
def Node.onBytes (n : Node) (cid : Id) (frame : ByteArray) (now : Nat) : IO (Node × Effects) := do
  match n.conn?, n.sealer? cid with
  | _, none => return (n, {})
  | conn?, some s =>
    match conn? cid, s.openFrame s.state frame with
    | some c, some (st, bytes) =>
      let n := n.setSealer cid { s with state := st }
      let (n, out) ← n.apply x cid (← (Conn.recv x.fam x.cfg n.ix c bytes now : SqlM F Step).run n.db) now
      n.finish x out now
    | _, _ => n.drop cid |>.finish x { drop := [cid] } now

/-- Bytes from the bare wire: a conn op (the handshake), or nothing. -/
def Node.onBare (n : Node) (addr bytes : ByteArray) (now : Nat) : IO (Node × Effects) := do
  match Op.decode bytes with
  | none => return (n, {})
  | some o =>
    let ops := intakeConn x.fam [o]
    if ops.isEmpty then return (n, {})
    let (n, _) ← n.write x ops
    let (n, out) ← n.store x (← (x.hooks.recv none addr o now).run n.db) true
    n.finish x out now

/-- The clock. -/
def Node.onTick (n : Node) (now : Nat) : IO (Node × Effects) := do
  let (n, out) ← n.store x (← (x.hooks.dial now).run n.db) true
  let mut n := n
  let mut out := out
  for (cid, _) in n.conns do
    match n.conn? cid with
    | none => pure ()
    | some c =>
      let (n', o) ← n.apply x cid (← (Conn.tick x.fam x.cfg n.ix c now : SqlM F Step).run n.db) now
      n := n'
      out := out ++ o
  n.finish x out now

/-- A local write: this device's own ops. -/
def Node.onWrite (n : Node) (ops : List Op) (now : Nat) : IO (Node × Effects) := do
  let (n, out) ← n.store x ops true
  n.finish x out now

end

end Engine.Sync
