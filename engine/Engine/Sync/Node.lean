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
- After each entry point the family's outbox (its `send` couriers) is
  handed out once and marked shipped. Sync's own round messages go out
  directly: they are transient and never stored.
- A connection that must drop is closed here and reported in `drop`.
-/
import Engine.Sync.Conn
import Engine.Sqlite

namespace Engine.Sync

/-- Where bytes go: a session, or an address on the bare wire. -/
inductive Route where
  | conn (cid : Id)
  | bare (addr : ByteArray)
  deriving Inhabited

/-- What the Connection family tells sync. -/
structure Hooks (F : Type) where
  /-- The rooms the peer on connection cid may see now. -/
  rooms : Id → SqlM F (List Id)
  /-- The local ops that record room r's first settle on connection cid. -/
  settled : Id → Id → List Op := fun _ _ => []
  /-- The local ops that record op o's arrival (on a session, or bare
  from an address) at a time. -/
  recv : Option Id → ByteArray → Op → Nat → List Op := fun _ _ _ _ => []
  /-- The family's send couriers waiting: id, route, bytes. -/
  outbox : SqlM F (List (Id × Route × ByteArray)) := pure []
  /-- The local ops that mark a courier handed out. -/
  shipped : Id → List Op := fun _ => []
  /-- What the family writes in answer to what is stored (views over
  lists, returning ops): run after every write, to a fixpoint. -/
  react : SqlM F (List Op) := pure []
  /-- What the family writes as time passes (dialing, retries). -/
  dial : Nat → SqlM F (List Op) := fun _ => pure []

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

/-- What to do: bytes to send, connections to drop. -/
structure Effects where
  send : List (Route × ByteArray) := []
  drop : List Id := []

instance : Append Effects := ⟨fun a b => ⟨a.send ++ b.send, a.drop ++ b.drop⟩⟩

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F)

def Node.boot (db : Db) (floor : Nat) : IO Node := do
  let ops ← (dumpOps (F := F)).run db
  return { db, ix := Index.ofOps x.fam ops, floor }

def Node.conn? (n : Node) (cid : Id) : Option Conn :=
  (n.conns.find? fun p => Decidable.decide (p.1 = cid)).map (·.2)

def Node.close (n : Node) (cid : Id) : Node :=
  { n with conns := n.conns.filter fun p => !Decidable.decide (p.1 = cid) }

def sends (cid : Id) (ops : List Op) : Effects := { send := ops.map fun o => (.conn cid, o.bytes) }

/-- One write turn of ops already through an intake; the index grows by
what is stored; the ids now stored. -/
def Node.write (n : Node) (ops : List Op) : IO (Node × List Id) := do
  if ops.isEmpty then return (n, [])
  (receive x.fam ops).run n.db
  let mut ix := n.ix
  let mut ids : List Id := []
  for o in ops do
    if (← (Store.getOp (F := F) o.id : SqlM F _).run n.db).isSome then
      ix := ix.add x.fam o
      ids := o.id :: ids
  return ({ n with ix }, ids.reverse)

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

/-- Apply a connection's step. -/
def Node.apply (n : Node) (cid : Id) (s : Step) (now : Nat) : IO (Node × Effects) := do
  if s.drop then return (n.close cid, { drop := [cid] })
  let n := { n with conns := n.conns.map fun p => if p.1 = cid then (cid, s.conn) else p }
  let n ← Node.settle x n (s.status.map (cid, ·))
  let (n, out) ← n.store x s.take false
  let (n, _) ← n.put x (s.take.flatMap fun o => x.hooks.recv (some cid) .empty o now) true
  return (n, sends cid s.send ++ out)

/-- A connection is open: say hello. -/
def Node.connect (n : Node) (cid : Id) (dialer : Bool) (now : Nat) : IO (Node × Effects) := do
  let s := Conn.open dialer (← (x.hooks.rooms cid).run n.db) n.floor now
  let n' : Node := { (n.close cid) with conns := (cid, s.conn) :: (n.close cid).conns }
  Node.flush x n' (sends cid s.send)

/-- Bytes from connection cid. -/
def Node.onBytes (n : Node) (cid : Id) (bytes : ByteArray) (now : Nat) : IO (Node × Effects) := do
  match n.conn? cid with
  | none => return (n, {})
  | some c =>
    let (n, out) ← n.apply x cid (← (Conn.recv x.fam x.cfg n.ix c bytes now : SqlM F Step).run n.db) now
    n.flush x out

/-- Bytes from the bare wire: a conn op (the handshake), or nothing. -/
def Node.onBare (n : Node) (addr bytes : ByteArray) (now : Nat) : IO (Node × Effects) := do
  match Op.decode bytes with
  | none => return (n, {})
  | some o =>
    let (n, ids) ← n.write x (intakeConn x.fam [o])
    if ids.isEmpty then return (n, {})
    let (n, _) ← n.put x (x.hooks.recv none addr o now) true
    n.flush x {}

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
  n.flush x out

/-- A local write: this device's own ops. -/
def Node.onWrite (n : Node) (ops : List Op) : IO (Node × Effects) := do
  let (n, out) ← n.store x ops true
  n.flush x out

end

end Engine.Sync
