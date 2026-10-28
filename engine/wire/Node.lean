/-
A node's sync: its room index and its open connections, with the entry
points a daemon calls (bytes from an address, the clock, local writes),
so the daemon is sockets, timers and discovery only. It runs in any
store (`m`: SQLite under the runner, held data in a proof's world) and
holds no protocol: which rooms a connection's peer may see, how an
arrival is answered, what the Connection family sends, and how frames
are sealed come from that family (`Hooks`).

The wire, after poc-17's frames: every payload's first byte says what
it is.
- `0x00` and an op's bytes: bare, the handshake's (conn ops only, taken
  through `intakeConn`).
- `0x01` and a sealed frame: the frame names its session, and opens
  only under that session's keys (`openFrame`); it carries a bundle of
  up to `bundle` bytes of the session's payloads, in order, each taken
  as if it came alone. A replayed frame re-delivers the same ops, which
  are taken once.
So a socket is not bound to a session: any address can carry any
session's frames, and a session's frames go to the address its last
frame came from (at first, the one its handshake ran on).

- Every write goes through `write`: one write turn (`Turn`) of the ops
  not already stored, through an intake; the index grows by them; they
  are offered on every connection whose peer may see them.
- A connection never steps on rooms read before: every step (a frame,
  the clock, an offer) first reads its rooms afresh from the family
  (`Node.refresh`), so a removal or an admission written since counts at
  once. What it sends and takes is then that step's rooms'
  (`recv_send`, `recv_take`).
- Sessions come from the family: after each entry point every
  connection its handshake has established is opened here, and every
  one it no longer lists is closed. A session dropped here (patience)
  is never reopened: a new connection needs a new handshake.
- After each entry point the family's outbox (its send couriers) is
  handed out once and marked shipped.
- Every id stored is reported (`stored`), so an app can re-read.
-/
import ops.sync.Conn
import engine.core.Held

namespace Engine.Sync

/-- Where an act's bytes go: a session, or an address on the bare wire. -/
inductive Route where
  | conn (cid : Id)
  | bare (addr : ByteArray)
  deriving Inhabited

/-- What the Connection family tells sync. -/
structure Hooks (F : Type) (m : Type → Type) [Monad m] where
  /-- The rooms the peer on connection cid may see now. -/
  rooms : Id → m (List Id)
  /-- The local ops that record room r's first settle on connection cid. -/
  settled : Id → Id → List Op := fun _ _ => []
  /-- What the family writes on op o's arrival (on a session, or bare
  from an address) at a time: called on every arrival, a repeat
  included, after it is stored. -/
  recv : Option Id → ByteArray → Op → Nat → m (List Op) := fun _ _ _ _ => pure []
  /-- The family's bare couriers waiting: id, address, op bytes. -/
  outbox : m (List (Id × ByteArray × ByteArray)) := pure []
  /-- What closing session cid purges (with its dependents): run when
  the session drops, or leaves `established`. -/
  closing : Id → m (List Id) := fun _ => pure []
  /-- Sessions the family no longer keeps (superseded by a redial, or
  the losing one of two): each is closed and purged like a drop. -/
  retired : m (List Id) := pure []
  /-- What the family writes in answer to what is stored: run after
  every write, to a fixpoint. -/
  react : m (List Op) := pure []
  /-- What the family writes as time passes (dialing, retries). -/
  dial : Nat → m (List Op) := fun _ => pure []
  /-- The sessions established: connection id, the address its
  handshake ran on, whether this side dialed. -/
  established : m (List (Id × ByteArray × Bool)) := pure []
  /-- Session cid's sealed frame for these bytes; none without keys. -/
  sealFor : Id → ByteArray → m (Option ByteArray)
  /-- A sealed frame's session and bytes, if it opens under that
  session's keys. -/
  openFrame : ByteArray → m (Option (Id × ByteArray))

/-- A node's sync setup: its family, the connection settings, and the
Connection family's hooks. -/
structure Sync (F : Type) (m : Type → Type) [Monad m] where
  fam : Family F
  cfg : Config := {}
  hooks : Hooks F m

structure Node where
  ix : Index
  floor : Nat
  conns : List (Id × Conn) := []
  /-- Where each session's frames go. -/
  addrs : List (Id × ByteArray) := []
  /-- The sessions opened from the family's `established`. -/
  managed : List Id := []
  /-- Sessions dropped here: never reopened. -/
  dropped : List Id := []
  /-- Ids stored since the last entry point returned. -/
  fresh : List Id := []

/-- What a step asks for, before sealing. -/
structure Acts where
  send : List (Route × ByteArray) := []
  drop : List Id := []

instance : Append Acts := ⟨fun a b => ⟨a.send ++ b.send, a.drop ++ b.drop⟩⟩

/-- What to do: payloads to send to addresses, sessions dropped, ids
stored. -/
structure Effects where
  send : List (ByteArray × ByteArray) := []
  drop : List Id := []
  stored : List Id := []

/-- The discriminators: a bare op, a sealed frame. -/
def bareTag : UInt8 := 0
def sealedTag : UInt8 := 1

def tagged (t : UInt8) (b : ByteArray) : ByteArray := ByteArray.mk #[t] ++ b

def Node.boot {F : Type} (fam : Family F) (ops : List Op) (floor : Nat) : Node :=
  { ix := Index.ofOps fam ops, floor }

def Node.conn? (n : Node) (cid : Id) : Option Conn :=
  (n.conns.find? fun p => Decidable.decide (p.1 = cid)).map (·.2)

def Node.addr? (n : Node) (cid : Id) : Option ByteArray :=
  (n.addrs.find? fun p => Decidable.decide (p.1 = cid)).map (·.2)

def Node.setAddr (n : Node) (cid : Id) (a : ByteArray) : Node :=
  { n with addrs := (cid, a) :: n.addrs.filter fun p => !Decidable.decide (p.1 = cid) }

def Node.close (n : Node) (cid : Id) : Node :=
  { n with
    conns := n.conns.filter fun p => !Decidable.decide (p.1 = cid)
    managed := n.managed.filter fun c => !Decidable.decide (c = cid) }

/-- A session ends here: closed, and never reopened. -/
def Node.drop (n : Node) (cid : Id) : Node :=
  let n := n.close cid
  { n with dropped := if has n.dropped cid then n.dropped else cid :: n.dropped }

def sends (cid : Id) (ops : List Op) : Acts := { send := ops.map fun o => (.conn cid, o.bytes) }

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] [Turn F m] (x : Sync F m)

/-- One write turn of the ops not already stored, already through an
intake; the index grows by them; the ids newly stored. -/
def Node.write (n : Node) (ops : List Op) : m (Node × List Id) := do
  let mut absent : List Op := []
  for o in ops do
    if !absent.any (·.id == o.id) then
      if (← Store.getOp (F := F) o.id).isNone then absent := o :: absent
  if absent.isEmpty then return (n, [])
  let news := absent.reverse
  Turn.turn x.fam news
  let mut ix := n.ix
  let mut ids : List Id := []
  for o in news do
    if (← Store.getOp (F := F) o.id).isSome then
      ix := ix.add x.fam o
      ids := o.id :: ids
  return ({ n with ix, fresh := n.fresh ++ ids.reverse }, ids.reverse)

/-- One write turn through `intake`. -/
def Node.put (n : Node) (ops : List Op) (mine : Bool) : m (Node × List Id) :=
  n.write x (intake x.fam mine ops)

/-- Write each settle the steps report. -/
def Node.settle (n : Node) (st : List (Id × Status)) : m Node := do
  let ops := st.flatMap fun (cid, .settled r) => x.hooks.settled cid r
  return (← n.put x ops true).1

/-- Connection c as its next step must see it: its rooms read afresh. -/
def Node.refresh (cid : Id) (c : Conn) : m Conn := do
  return c.setRooms (← x.hooks.rooms cid)

/-- Offer stored ids on every connection. -/
def Node.fanout (n : Node) (ids : List Id) : m (Node × Acts) := do
  let mut conns : List (Id × Conn) := []
  let mut out : Acts := {}
  let mut st : List (Id × Status) := []
  for (cid, c) in n.conns do
    let c ← Node.refresh x cid c
    let s ← Conn.filed x.fam x.cfg c ids
    conns := (cid, s.conn) :: conns
    out := out ++ sends cid s.send
    st := st ++ s.status.map (cid, ·)
  let n ← Node.settle x { n with conns := conns.reverse } st
  return (n, out)

/-- Store ops (a local write, or a peer's) and offer them on; then
write what the family answers, until it answers nothing (at most 16
rounds). -/
def Node.store (n : Node) (ops : List Op) (mine : Bool) : m (Node × Acts) := do
  let (n, ids) ← n.put x ops mine
  if ids.isEmpty then return (n, {})
  let (n, out) ← n.fanout x ids
  let mut n := n
  let mut out := out
  for _ in [0:16] do
    let more ← x.hooks.react
    if more.isEmpty then break
    let (n', ids) ← n.put x more true
    if ids.isEmpty then break
    let (n'', o) ← n'.fanout x ids
    n := n''
    out := out ++ o
  return (n, out)

/-- Open a session's connection: say hello. -/
def Node.open (n : Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    m (Node × Acts) := do
  let s := Conn.open dialer (← x.hooks.rooms cid) n.floor now
  let n := (n.close cid).setAddr cid addr
  return ({ n with conns := (cid, s.conn) :: n.conns }, sends cid s.send)

/-- Follow the family's sessions: open the newly established, close the
ones it no longer lists. -/
def Node.follow (n : Node) (now : Nat) : m (Node × Acts) := do
  let est ← x.hooks.established
  let mut n := n
  let mut out : Acts := {}
  for cid in n.managed do
    if !est.any (fun e => Decidable.decide (e.1 = cid)) then
      n := n.drop cid
      out := out ++ { drop := [cid] }
  for (cid, addr, dialer) in est do
    if !has n.managed cid && !has n.dropped cid then
      let (n', o) ← n.open x cid addr dialer now
      n := { n' with managed := cid :: n'.managed }
      out := out ++ o
  return (n, out)

/-- Hand out the family's outbox once, and mark it shipped. -/
def Node.flush (n : Node) (out : Acts) : m (Node × Acts) := do
  let box ← x.hooks.outbox
  if box.isEmpty then return (n, out)
  -- Handed out: the couriers are purged (poc-17's shipped courier).
  Turn.purge x.fam (box.map (·.1)) false
  return (n, out ++ { send := box.map fun (_, a, b) => (.bare a, b) })

/-- Payloads in bundles of at most `max` bytes, in order (a payload
longer than `max` goes alone). -/
def bundles (max : Nat) : List ByteArray → List (List ByteArray)
  | [] => []
  | b :: rest =>
    match bundles max rest with
    | [] => [[b]]
    | g :: gs =>
      if b.size + (g.foldl (· + ·.size) 0) ≤ max then (b :: g) :: gs else [b] :: g :: gs

/-- Address and seal what goes out: the bare sends first (the
handshake's replies go before a session's first frame), then each
session's payloads in bundles, one sealed frame each. A send on a
session with no address or no keys is dropped. -/
def Node.seal (n : Node) (out : Acts) : m (List (ByteArray × ByteArray)) := do
  let mut sent : List (ByteArray × ByteArray) := []
  let mut cids : List Id := []
  for (r, b) in out.send do
    match r with
    | .bare a => sent := (a, tagged bareTag b) :: sent
    | .conn cid => if !has cids cid then cids := cid :: cids
  for cid in cids.reverse do
    let payloads := out.send.filterMap fun (r, b) => match r with
      | .conn c => if c = cid then some b else none
      | .bare _ => none
    if let some a := n.addr? cid then
      for g in bundles x.cfg.bundle payloads do
        if let some f ← x.hooks.sealFor cid (Codec.encode g) then
          sent := (a, tagged sealedTag f) :: sent
  return sent.reverse

/-- The common end of every session: ask the family for its secrets,
then purge them and their dependents, with disk scrubbing. -/
def Node.endSession (cid : Id) : m Unit := do
  let ids ← x.hooks.closing cid
  if !ids.isEmpty then Turn.purge x.fam ids true

/-- Every entry point ends here: follow the sessions, hand out the
outbox (the handshake's bare replies go before a new session's first
frame), seal, and report what was stored. -/
def Node.finish (n : Node) (out : Acts) (now : Nat) : m (Node × Effects) := do
  let (n, o) ← n.follow x now
  let (n, out) ← n.flush x out
  let out := out ++ o
  let retired ← x.hooks.retired
  let n := retired.foldl Node.drop n
  let out := { out with drop := out.drop ++ retired }
  let sent ← n.seal x out
  -- A session that dropped, or left `established`, is forgotten: its
  -- secrets are purged, and a redial makes a new one.
  for cid in out.drop do
    Node.endSession x cid
  return ({ n with fresh := [] }, { send := sent, drop := out.drop, stored := n.fresh })

/-- Loss of the transport ends all sessions routed through that address.
The same finish path as a protocol drop purges their keys. -/
def Node.onClose (n : Node) (addr : ByteArray) (now : Nat) : m (Node × Effects) := do
  let ids := n.conns.filterMap fun (cid, _) =>
    if n.addr? cid == some addr then some cid else none
  let n := ids.foldl Node.drop n
  n.finish x { drop := ids } now

/-- Apply a connection's step. -/
def Node.apply (n : Node) (cid : Id) (s : Step) (now : Nat) : m (Node × Acts) := do
  if s.drop then return (n.drop cid, { drop := [cid] })
  let n := { n with conns := n.conns.map fun p => if p.1 = cid then (cid, s.conn) else p }
  let n ← Node.settle x n (s.status.map (cid, ·))
  let (n, out) ← n.store x s.take false
  let mut arrived : List Op := []
  for o in s.take do
    arrived := arrived ++ (← x.hooks.recv (some cid) .empty o now)
  let (n, out') ← n.store x arrived true
  return (n, sends cid s.send ++ out ++ out')

/-- A connection opened without a handshake: the in-memory harness's. -/
def Node.connect (n : Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    m (Node × Effects) := do
  let (n, out) ← n.open x cid addr dialer now
  n.finish x out now

/-- A sealed frame from an address, as `openFrame` gave it: its session
and bytes, or none if it did not open. It sees only what opened, so
nothing of a frame is decoded before its AEAD check passes. A frame that
did not open, or one for a session not open here, is ignored. -/
def Node.onSealed (n : Node) (addr : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) :
    m (Node × Effects) := do
  match opened with
  | none => return (n, {})
  | some (cid, bundle) =>
    match n.conn? cid, (Codec.decode bundle : Option (List ByteArray)) with
    | some _, some inner =>
      let mut n := n.setAddr cid addr
      let mut out : Acts := {}
      for b in inner do
        if let some c := n.conn? cid then
          let c ← Node.refresh x cid c
          let (n', o) ← n.apply x cid (← Conn.recv x.fam x.cfg n.ix c b now) now
          n := n'
          out := out ++ o
      n.finish x out now
    | _, _ => return (n, {})

/-- A payload from an address: a bare op (the handshake's), or a sealed
frame on a session (`onSealed`). Anything else is ignored. -/
def Node.onFrame (n : Node) (addr bytes : ByteArray) (now : Nat) : m (Node × Effects) := do
  let body := bytes.extract 1 bytes.size
  match (bytes[0]? : Option UInt8) with
  | some 0 =>
    match Op.decode body with
    | none => return (n, {})
    | some o =>
      let ops := intakeConn x.fam [o]
      if ops.isEmpty then return (n, {})
      let (n, _) ← n.write x ops
      let (n, out) ← n.store x (← x.hooks.recv none addr o now) true
      n.finish x out now
  | some 1 => n.onSealed x addr (← x.hooks.openFrame body) now
  | _ => return (n, {})

/-- The clock. -/
def Node.onTick (n : Node) (now : Nat) : m (Node × Effects) := do
  let (n, out) ← n.store x (← x.hooks.dial now) true
  let mut n := n
  let mut out := out
  for (cid, _) in n.conns do
    match n.conn? cid with
    | none => pure ()
    | some c =>
      let c ← Node.refresh x cid c
      let (n', o) ← n.apply x cid (← Conn.tick x.fam x.cfg n.ix c now) now
      n := n'
      out := out ++ o
  n.finish x out now

/-- A local write: this device's own ops. -/
def Node.onWrite (n : Node) (ops : List Op) (now : Nat) : m (Node × Effects) := do
  let (n, out) ← n.store x ops true
  n.finish x out now

end

/-- Sealing for the in-memory harness only: a frame is its session and
the bytes, in the clear. -/
def plainSeal {m : Type → Type} [Monad m] (cid : Id) (b : ByteArray) : m (Option ByteArray) :=
  pure (some (Codec.encode (cid, b)))

def plainOpen {m : Type → Type} [Monad m] (f : ByteArray) : m (Option (Id × ByteArray)) :=
  pure (Codec.decode f)

end Engine.Sync
