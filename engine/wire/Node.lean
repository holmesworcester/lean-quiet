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
  (`recv_send`, `recv_take`). Where the node stores ops and on the clock
  it also gives the connection's notices (`filedGive`, `tickGive`), and
  writes the local ops returned by onGiven for each notice given.
- Sessions come from the family: after each entry point every
  connection its handshake has established is opened here, and every
  one it no longer lists is closed. A session dropped here (silence)
  is never reopened: a new connection needs a new handshake.
- After each entry point the family's outbox (its send couriers) is
  handed out once and marked shipped.
- Every stored id and purge root is reported, so an app can re-read.
- Every id stored is reported (`stored`), so an app can re-read.
- What a step sends takes one of two lanes (docs/SYNC.md, "Lanes"):
  urgent (messages naming few ids, `wireLane`; the stream's offers; and
  the wanted ops this node just wrote) or serve (the rest: the queue of
  the peer's wants, and long offers and wants). Each session's queue is
  served once a step, after the step's payloads (`serveOwed`), within
  the room its socket has (`Sync.room`). Each lane's payloads are
  sealed in frames of their own, the serve lane's last (`Effects.serve`
  counts them), so the runner can send urgent frames ahead of a
  backlog.
-/
import engine.sync.Notice
import engine.core.Held
import engine.wire.Lanes
import engine.sync.Sweep
import engine.wire.RetryOrder

namespace Engine.Sync

/-- Where an act's bytes go: a session, or an address on the bare wire. -/
inductive Route where
  | conn (cid : Id)
  | bare (addr : ByteArray)
  deriving Inhabited, DecidableEq

/-- What the Connection family tells sync. -/
structure Hooks (F : Type) (m : Type → Type) [Monad m] where
  /-- What connection cid carries now: the rooms its peer may see,
  synced, and the notices it is to give (engine/sync/Notice.lean). -/
  rooms : Id → m (List Room)
  /-- Local ops recording notice x given on connection cid. -/
  onGiven : Id → Id → List Op := fun _ _ => []
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
  /-- Stable authenticated remote identity for retry progress across sessions.
  Standalone fixed-session interpreters use their session id by default. -/
  retryKey : Id → m (Option Id) := fun cid => pure (some cid)

/-- A node's sync setup: its family, the connection settings, and the
Connection family's hooks. -/
structure Sync (F : Type) (m : Type → Type) [Monad m] where
  fam : Family F
  cfg : Config := {}
  hooks : Hooks F m
  /-- Serve-lane bytes the transport has room for at an address: the
  runner's flow control (none, as in a proof's world: `cfg.burst` a
  step). -/
  room : ByteArray → Option Nat := fun _ => none
  /-- Durable retry source. The production runner always supplies SQLite's
  catalog; explicit interpreters may supply their own read-only catalog. -/
  catalog : Option (Catalog m) := none
  retryStore : Option (RetryStore m) := none
  /-- Independent reserved transport room; production supplies a vacant
  one-frame slot, rather than competing with ordinary output. -/
  retryRoom : ByteArray → Option Nat := fun _ => none
  /-- Production commits a retry ticket after native write completion.
  Direct node interpreters retain immediate cursor bookkeeping. -/
  deferredRetries : Bool := false
  /-- Native silence grace may defer timed work for an already-admitted
  source. Dial/reaction, authorization and authenticated retirement still
  run. Pure/default callers service every connection as before. -/
  tickReady : Id → Bool := fun _ => true

structure Node where
  ix : Index
  floor : Nat
  conns : List (Id × Conn) := []
  /-- Stable catalog admission order, independent of ordinary connection work. -/
  retryOrder : List Id := []
  /-- Where each session's frames go. -/
  addrs : List (Id × ByteArray) := []
  /-- The sessions opened from the family's `established`. -/
  managed : List Id := []
  /-- Sessions dropped here: never reopened. -/
  dropped : List Id := []
  /-- Ids stored since the last entry point returned. -/
  fresh : List Id := []
  /-- Purge roots since the last entry point, including shipped couriers. -/
  purged : List Id := []
  /-- Ids this node wrote, newest first, each with when (at most
  `hotCap`): a want for one within `hotMs` is answered urgent. -/
  hot : List (Id × Nat) := []
  /-- One constant-size retry cursor per live session. -/
  sweeps : List (Id × Sweep) := []

structure RetryOffer where
  cid : Id
  payload : ByteArray
  ticket : RetryTicket

/-- What a step asks for, before sealing. -/
structure Acts where
  send : List (Route × ByteArray) := []
  drop : List Id := []
  /-- Payloads of the serve lane. -/
  serve : List (Route × ByteArray) := []
  /-- These payloads also occur in serve, but use singleton reserved frames. -/
  retry : List RetryOffer := []
  /-- Notice payloads must survive ordinary-data queue pressure. -/
  critical : List Id := []

instance : Append Acts := ⟨fun a b =>
  ⟨a.send ++ b.send, a.drop ++ b.drop, a.serve ++ b.serve,
    a.retry ++ b.retry, a.critical ++ b.critical⟩⟩

/-- What to do: payloads to send to addresses, sessions dropped, ids
stored. -/
structure Effects where
  send : List (ByteArray × ByteArray) := []
  drop : List Id := []
  stored : List Id := []
  /-- Every root passed to a purge, with its dependents invalidated by the store. -/
  purged : List Id := []
  /-- How many of `send`'s payloads, at its end, are the serve lane's
  (the rest are urgent). -/
  serve : Nat := 0
  /-- Tickets correspond, in order, to the final frames of send. -/
  retry : List RetryTicket := []
  /-- Addresses carrying notices, separately buffered from normal data. -/
  critical : List ByteArray := []

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
    sweeps := n.sweeps.filter fun p => !Decidable.decide (p.1 = cid)
    managed := n.managed.filter fun c => !Decidable.decide (c = cid) }

/-- A session ends here: closed, and never reopened. -/
def Node.drop (n : Node) (cid : Id) : Node :=
  let n := n.close cid
  { n with dropped := if has n.dropped cid then n.dropped else cid :: n.dropped }

def sends (cid : Id) (ops : List Op) : Acts := { send := ops.map fun o => (.conn cid, o.bytes) }

section
variable {F : Type} {m : Type → Type} [Monad m] (x : Sync F m)

/-- A wire op naming at most `urgentIds` ids (at least one) is urgent;
a longer one is served. -/
def wireLane (o : Op) : Lane :=
  if o.reqs.length ≤ max x.cfg.urgentIds 1 then .urgent else .serve

/-- The ids this node wrote within `hotMs`: a want for one is served
urgent (`Node.serveOwed`). -/
def Node.hotIds (n : Node) (now : Nat) : List Id :=
  n.hot.filterMap fun p => if now ≤ p.2 + x.cfg.hotMs then some p.1 else none

end

/-- Session cid's sends, each in its lane, in order. -/
def split (lane : Op → Lane) (cid : Id) (ops : List Op) : Acts :=
  { send := (ops.filter fun o => lane o = .urgent).map fun o => (.conn cid, o.bytes)
    serve := (ops.filter fun o => lane o = .serve).map fun o => (.conn cid, o.bytes) }

section
variable {F : Type} {m : Type → Type} [Monad m] (x : Sync F m)

/-- This node's own ops just stored, hot from `now`. -/
def Node.heat (n : Node) (ids : List Id) (now : Nat) : Node :=
  { n with hot := ((ids.reverse.map (·, now)) ++ n.hot.filter fun p => now ≤ p.2 + x.cfg.hotMs).take x.cfg.hotCap }

end

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] [Turn F m] (x : Sync F m)

/-- Every purge the node runs carries its roots to the app's notices. -/
def Effects.purge (ids : List Id) (scrub : Bool) : m Effects := do
  if !ids.isEmpty then Turn.purge x.fam ids scrub
  return { purged := ids }

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

/-- Persist each notice acknowledgment through the family. -/
def Node.recordGiven (n : Node) (st : List (Id × Id)) : m Node := do
  let ops := st.flatMap fun (cid, v) => x.hooks.onGiven cid v
  return (← n.put x ops true).1

/-- Connection c as its next step must see it: its rooms and notices
read afresh. -/
def Node.refresh (cid : Id) (c : Conn) : m Conn := do
  return c.carry (← x.hooks.rooms cid)

/-- Offer stored ids on every connection. -/
def Node.fanout (n : Node) (ids : List Id) : m (Node × Acts) := do
  let mut conns : List (Id × Conn) := []
  let mut out : Acts := {}
  let mut given : List (Id × Id) := []
  for (cid, c) in n.conns do
    let c ← Node.refresh x cid c
    let s ← Conn.filedGive x.fam x.cfg c ids
    conns := (cid, s.conn) :: conns
    out := out ++ { sends cid s.send with critical := if s.given.isEmpty then [] else [cid] }
    given := given ++ s.given.map (cid, ·)
  let n ← Node.recordGiven x { n with conns := conns.reverse } given
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
  let s := Conn.open dialer (Room.syncs (← x.hooks.rooms cid)) n.floor now
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
  let e ← Effects.purge x (box.map (·.1)) false
  return ({ n with purged := n.purged ++ e.purged },
    out ++ { send := box.map fun (_, a, b) => (.bare a, b) })

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

/-- Remember output time once, including stream offers from local writes. -/
def Node.sent (n : Node) (out : Acts) (now : Nat) : Node :=
  { n with conns := n.conns.map fun (cid, c) =>
      (cid, if out.send.any (fun (r, _) => match r with
        | .conn i => i == cid | .bare _ => false) then { c with sent := now } else c) }

/-- The common end of every session: ask the family for its secrets,
then purge them and their dependents, with disk scrubbing. -/
def Node.endSession (cid : Id) : m Effects := do
  Effects.purge x (← x.hooks.closing cid) true

/-- Each reserved payload is sealed alone, paired with its durable cursor
ticket only if the actual session seal produced a frame. -/
def Node.sealRetries (n : Node) (retries : List RetryOffer) :
    m (List (ByteArray × ByteArray) × List RetryTicket) := do
  let mut reserved : List (ByteArray × ByteArray) := []
  let mut tickets : List RetryTicket := []
  for r in retries do
    let frames ← n.seal x { send := [(.conn r.cid, r.payload)] }
    reserved := reserved ++ frames
    tickets := tickets ++ frames.map (fun _ => r.ticket)
  return (reserved, tickets)

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
  -- A marker cannot introduce any payload not already authorized in Acts.
  let retries := out.retry.filter fun r => out.serve.contains (.conn r.cid, r.payload)
  let ordinary := out.serve.filter fun p => !retries.any fun r => p == (.conn r.cid, r.payload)
  let served ← n.seal x { send := ordinary }
  let (reserved, tickets) ← n.sealRetries x retries
  let n := n.sent { out with send := out.send ++ out.serve } now
  -- A session that dropped, or left `established`, is forgotten: its
  -- secrets are purged, and a redial makes a new one.
  let mut purged := n.purged
  for cid in out.drop do
    purged := purged ++ (← Node.endSession x cid).purged
  return ({ n with fresh := [], purged := [] },
    { send := sent ++ served ++ reserved, drop := out.drop, stored := n.fresh, purged,
      serve := served.length + reserved.length, retry := tickets,
      critical := out.critical.filterMap n.addr? })

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
  let n : Node := { n with conns := n.conns.map fun p => if p.1 = cid then (cid, s.conn) else p }
  let n ← n.recordGiven x (s.given.map (cid, ·))
  let (n, out) ← n.store x s.take false
  let mut arrived : List Op := []
  for o in s.take do
    arrived := arrived ++ (← x.hooks.recv (some cid) .empty o now)
  let (n, out') ← n.store x arrived true
  let replies := { split (wireLane x) cid s.send with
    critical := if s.given.isEmpty then [] else [cid] }
  return (n, replies ++ out ++ out')

/-- Serve session cid's queue (`Conn.serveOwed`): the ops it wants that
this node wrote within `hotMs` go urgent; then, in the serve lane, as
many bytes as the transport has room for at its address (`x.room`), or
`cfg.burst` without a transport. -/
def Node.serveOwed (n : Node) (cid : Id) (now : Nat) : m (Node × Acts) := do
  match n.conn? cid with
  | none => return (n, {})
  | some c =>
    if c.owed.isEmpty then return (n, {})
    let c ← Node.refresh x cid c
    let budget := ((n.addr? cid).bind x.room).getD x.cfg.burst
    let (c, urgent, bulk) ← c.serveOwed x.fam x.cfg budget (n.hotIds x now)
    return ({ n with conns := n.conns.map fun p => if p.1 = cid then (cid, c) else p },
      { send := urgent.map fun o => (.conn cid, o.bytes), serve := bulk.map fun o => (.conn cid, o.bytes) })

/-- Conservative bytes already produced for one socket, including a whole
production envelope per payload. Bundling can only reduce that reservation. -/
def Node.reserved (n : Node) (out : Acts) (addr : ByteArray) : Nat :=
  ((out.send ++ out.serve).map fun (route, bytes) =>
    let destination := match route with
      | .bare a => some a
      | .conn cid => n.addr? cid
    if destination = some addr then (Codec.encode [bytes]).size + 74 else 0).sum

def Node.afterActs (n : Node) (out : Acts) : Sync F m :=
  { x with
    room := fun addr => if x.catalog.isNone then x.room addr
      else some ((x.room addr).getD maxFrame - n.reserved out addr)
    retryRoom := fun addr => if out.retry.any (fun r => n.addr? r.cid == some addr)
      then some 0 else x.retryRoom addr }

/-- Retry a single durable catalog position for this session. Neither lost
round openings nor a full asked/owed cache can suppress this path. -/
def Node.sweep (n : Node) (cid : Id) : m (Node × Acts) := do
  let some catalog := x.catalog | return (n, {})
  let some c := n.conn? cid | return (n, {})
  let c ← Node.refresh x cid c
  let some peer ← x.hooks.retryKey cid | return (n, {})
  let cursor ← match x.retryStore with
    | some store => store.load peer
    | none => pure (((n.sweeps.find? (fun p => p.1 == cid)).map Prod.snd).getD {})
  let room := if x.deferredRetries then ((n.addr? cid).bind x.retryRoom).getD 0
    else ((n.addr? cid).bind x.room).getD maxFrame
  let before := cursor
  let (cursor, offered) ← Sweep.run catalog cursor (c.shows x.fam) room
  let n ← match x.retryStore with
    | some store => do
      if !x.deferredRetries || offered.isNone then store.save peer cursor
      pure n
    | none => pure { n with sweeps := (cid, cursor) :: n.sweeps.filter (fun p => p.1 != cid) }
  return (n, {
    serve := offered.toList.map (fun o => (.conn cid, o.bytes))
    retry := if x.deferredRetries then offered.toList.map fun o =>
      ⟨cid, o.bytes, ⟨peer, before, cursor⟩⟩ else [] })

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
      let (n', o) ← n.serveOwed x cid now
      n'.finish x (out ++ o) now
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

/-- Catalog retries have their own stable admission order. Only sessions
whose ordinary timed step ran are eligible in this pass; native silence grace
still gives an admitted frame its original bounded selection opportunity. -/
def Node.sweepAll (n : Node) (ready : List Id) (out : Acts) : m (Node × Acts) := do
  let order := RetryOrder.reconcile (n.conns.map Prod.fst) n.retryOrder
  let mut n := n
  let mut out := out
  let mut offered := []
  let mut claimed := out.retry.filterMap (fun r => n.addr? r.cid)
  for cid in order do
    if !ready.contains cid then continue
    -- A rejected candidate retains its durable cursor. Candidate payloads are
    -- consumed immediately, so this never retains a frame for every session.
    let sx := if x.deferredRetries then x else n.afterActs x out
    let before := n.sweeps
    let (next, retry) ← n.sweep sx cid
    let candidate := !retry.retry.isEmpty
    let decision := RetryOrder.scan next.addr? (fun _ => candidate) claimed [cid]
    let accepted := !decision.1.isEmpty
    n := if x.deferredRetries && candidate && !accepted then { next with sweeps := before } else next
    claimed := decision.2
    if x.deferredRetries && !accepted then continue
    out := out ++ retry
    offered := offered ++ retry.retry.map (·.cid)
  return ({ n with retryOrder := RetryOrder.offered offered order }, out)

/-- The clock. Ordinary connection work keeps its original traversal order;
catalog retries then use the independent stable admission queue. -/
def Node.onTickReserved (n : Node) (now : Nat) : m (Node × Effects) := do
  let (n, out) ← n.store x (← x.hooks.dial now) true
  let mut n := n
  let mut out := out
  let mut ready := []
  for (cid, _) in n.conns do
    match n.conn? cid with
    | none => pure ()
    | some c =>
      let c ← Node.refresh x cid c
      -- Fresh authenticated notices bypass silence grace.
      if !x.tickReady cid && c.notices.isEmpty then continue
      ready := ready ++ [cid]
      let (n', o) ← n.apply x cid (← Conn.tickGive x.fam x.cfg n.ix c now) now
      let (n', o') ← n'.serveOwed (n'.afterActs x (out ++ o)) cid now
      n := n'
      out := out ++ o ++ o'
  let (next, acts) ← n.sweepAll x ready out
  next.finish x acts now

/-- Direct interpreters retain the original immediate-cursor clock semantics. -/
def Node.onTickDirect (n : Node) (now : Nat) : m (Node × Effects) := do
  let (n, out) ← n.store x (← x.hooks.dial now) true
  let mut n := n
  let mut out := out
  for (cid, _) in n.conns do
    match n.conn? cid with
    | none => pure ()
    | some c =>
      let c ← Node.refresh x cid c
      -- Fresh authenticated notices bypass silence grace.
      if !x.tickReady cid && c.notices.isEmpty then continue
      let (n', o) ← n.apply x cid (← Conn.tickGive x.fam x.cfg n.ix c now) now
      let (n', retry) ← n'.sweep (n'.afterActs x (out ++ o)) cid
      let (n', o') ← n'.serveOwed (n'.afterActs x (out ++ o ++ retry)) cid now
      n := n'
      out := out ++ o ++ retry ++ o'
  n.finish x out now

/-- Production deferred transport uses stable retry admission. The direct
interpreter's previous output budget/order is preserved exactly. -/
def Node.onTick (n : Node) (now : Nat) : m (Node × Effects) :=
  if x.deferredRetries then n.onTickReserved x now else n.onTickDirect x now

/-- A local write: this device's own ops, hot from now on. -/
def Node.onWrite (n : Node) (ops : List Op) (now : Nat) : m (Node × Effects) := do
  let (n, out) ← n.store x ops true
  (n.heat x n.fresh now).finish x out now

end

/-- Sealing for the in-memory harness only: a frame is its session and
the bytes, in the clear. -/
def plainSeal {m : Type → Type} [Monad m] (cid : Id) (b : ByteArray) : m (Option ByteArray) :=
  pure (some (Codec.encode (cid, b)))

def plainOpen {m : Type → Type} [Monad m] (f : ByteArray) : m (Option (Id × ByteArray)) :=
  pure (Codec.decode f)

end Engine.Sync
