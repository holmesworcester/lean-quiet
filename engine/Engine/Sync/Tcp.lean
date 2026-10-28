/-
The TCP runner: the one loop a phone app or a desktop daemon runs, so
neither carries socket code.

- It listens on a port and dials the bare addresses ("a.b.c.d:port")
  the node sends to; frames queue until the dial completes.
- Every payload is framed (`frame`, `unframe`: a 4-byte length, at most
  1 MiB; a longer one closes the socket).
- A socket is bare until the node binds it to a session (`bind`); its
  frames go to `onBare` until then and to `onBytes` after. An accepted
  socket's address is its peer's "ip:port", so the family's reply to
  that address goes back on the same socket.
- An unbound socket silent for `bareIdle` ms is closed: a join request
  waiting for approval is resent every tick, so a live one is never
  idle that long.
- The app's writes come in through `Runner.write`; every id the node
  stores goes to the app's `notify`.

One task owns the node and its SQLite connection; the listener and one
reader per socket feed it events through a channel.
-/
import Engine.Sync.Node
import Engine.Sync.Frame
import Std.Async.TCP
import Std.Sync.Channel

namespace Engine.Sync
open Std Std.Async Std.Net

/-- "a.b.c.d:port". -/
def addrText : SocketAddress → String
  | .v4 a => s!"{".".intercalate (a.addr.octets.toList.map (toString ·.toNat))}:{a.port}"
  | .v6 a => s!"[v6]:{a.port}"

def parseAddr (s : String) : Option SocketAddress :=
  match s.splitOn ":" with
  | [ip, port] =>
    match (ip.splitOn ".").map String.toNat?, port.toNat? with
    | [some a, some b, some c, some d], some p =>
      if a < 256 && b < 256 && c < 256 && d < 256 && p < 65536 then
        some (.v4 ⟨IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8, p.toUInt16⟩)
      else none
    | _, _ => none
  | _ => none

inductive Event where
  | frame (sock : Nat) (payload : ByteArray)
  | closed (sock : Nat)
  | accepted (c : TCP.Socket.Client) (peer : ByteArray)
  | dialed (addr : ByteArray) (c : Option TCP.Socket.Client)
  | write (ops : List Op)
  | stop

instance : Inhabited Event := ⟨.stop⟩

structure Sock where
  id : Nat
  client : TCP.Socket.Client
  addr : ByteArray
  cid : Option Id := none
  heard : Nat

structure RunState where
  node : Node
  socks : List Sock := []
  next : Nat := 0
  /-- Frames waiting for a dial to complete, by address. -/
  pending : List (ByteArray × List ByteArray) := []
  lastTick : Nat := 0

structure RunConfig where
  tickMs : Nat := 200
  bareIdle : Nat := 600000

/-- Read frames from a socket into the channel until it closes. -/
def reader (ch : Std.Channel Event) (sid : Nat) (c : TCP.Socket.Client) : IO Unit := do
  let mut buf := ByteArray.empty
  repeat
    match ← (c.recv? 65536).block.toBaseIO with
    | .ok (some chunk) =>
      buf := buf ++ chunk
      let mut more := true
      while more do
        match unframe buf with
        | .frame p rest =>
          discard <| ch.trySend (.frame sid p)
          buf := rest
        | .more => more := false
        | .tooBig =>
          discard <| ch.trySend (.closed sid)
          return
    | _ =>
      discard <| ch.trySend (.closed sid)
      return

/-- Accept connections into the channel. -/
def acceptor (ch : Std.Channel Event) (srv : TCP.Socket.Server) : IO Unit := do
  repeat
    match ← srv.accept.block.toBaseIO with
    | .ok c =>
      let peer := match ← c.getPeerName.toBaseIO with
        | .ok a => addrText a
        | .error _ => "?"
      discard <| ch.trySend (.accepted c peer.toUTF8)
    | .error _ => IO.sleep 100

/-- Dial an address; the outcome goes into the channel. -/
def dialOut (ch : Std.Channel Event) (addr : ByteArray) : IO Unit := do
  match String.fromUTF8? addr >>= parseAddr with
  | none => discard <| ch.trySend (.dialed addr none)
  | some sa =>
    let r ← (do
      let c ← TCP.Socket.Client.mk
      c.connect sa
      pure c : Async TCP.Socket.Client).block.toBaseIO
    match r with
    | .ok c => discard <| ch.trySend (.dialed addr (some c))
    | .error _ => discard <| ch.trySend (.dialed addr none)

def sendOn (c : TCP.Socket.Client) (payload : ByteArray) : IO Bool := do
  match ← (c.send (frame payload)).block.toBaseIO with
  | .ok _ => return true
  | .error _ => return false

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F) (ch : Std.Channel Event)
  (notify : List Id → IO Unit)

def RunState.sockOf (st : RunState) (p : Sock → Bool) : Option Sock := st.socks.find? p

def RunState.drop (st : RunState) (sid : Nat) : RunState :=
  { st with socks := st.socks.filter (·.id != sid) }

def RunState.addSock (st : RunState) (c : TCP.Socket.Client) (addr : ByteArray) (now : Nat) :
    IO (RunState × Nat) := do
  let sid := st.next
  let _ ← IO.asTask (prio := .dedicated) (reader ch sid c)
  return ({ st with socks := { id := sid, client := c, addr, heard := now } :: st.socks, next := sid + 1 }, sid)

/-- Carry out what the node asked for. -/
def RunState.apply (st : RunState) (e : Effects) : IO RunState := do
  let mut st := st
  for (cid, addr) in e.bind do
    st := { st with socks := st.socks.map fun s =>
      if s.addr == addr && s.cid.isNone then { s with cid := some cid } else s }
  for (r, b) in e.send do
    match r with
    | .conn cid =>
      if let some s := st.sockOf (fun s => s.cid == some cid) then
        unless ← sendOn s.client b do st := st.drop s.id
    | .bare addr =>
      match st.sockOf (fun s => s.addr == addr) with
      | some s => unless ← sendOn s.client b do st := st.drop s.id
      | none =>
        match st.pending.find? (·.1 == addr) with
        | some _ =>
          st := { st with pending := st.pending.map fun (a, fs) => if a == addr then (a, fs ++ [b]) else (a, fs) }
        | none =>
          st := { st with pending := (addr, [b]) :: st.pending }
          let _ ← IO.asTask (prio := .dedicated) (dialOut ch addr)
  for cid in e.drop do
    if let some s := st.sockOf (fun s => s.cid == some cid) then
      discard <| s.client.shutdown.block.toBaseIO
      st := st.drop s.id
  unless e.stored.isEmpty do notify e.stored
  return st

/-- Handle one event; false to stop. -/
def RunState.handle (st : RunState) (ev : Event) (now : Nat) : IO (Option RunState) := do
  match ev with
  | .stop => return none
  | .frame sid p =>
    match st.sockOf (·.id == sid) with
    | none => return some st
    | some s =>
      let st := { st with socks := st.socks.map fun (s' : Sock) => if s'.id == sid then { s' with heard := now } else s' }
      let (n, e) ← match s.cid with
        | some cid => st.node.onBytes x cid p now
        | none => st.node.onBare x s.addr p now
      some <$> ({ st with node := n }).apply ch notify e
  | .closed sid =>
    match st.sockOf (·.id == sid) with
    | none => return some st
    | some s =>
      let st := st.drop sid
      return some (match s.cid with
        | some cid => { st with node := st.node.drop cid }
        | none => st)
  | .accepted c peer => return some (← st.addSock ch c peer now).1
  | .dialed addr none => return some { st with pending := st.pending.filter (·.1 != addr) }
  | .dialed addr (some c) =>
    let (st, sid) ← st.addSock ch c addr now
    let frames := (st.pending.find? (·.1 == addr)).map (·.2) |>.getD []
    let mut st := { st with pending := st.pending.filter (·.1 != addr) }
    for b in frames do
      if let some s := st.sockOf (·.id == sid) then
        unless ← sendOn s.client b do st := st.drop sid
    return some st
  | .write ops =>
    let (n, e) ← st.node.onWrite x ops now
    some <$> ({ st with node := n }).apply ch notify e

/-- The loop: events as they come, the clock every `tickMs`. -/
def runLoop (cfg : RunConfig) (st : RunState) : IO Unit := do
  let mut st := st
  repeat
    let now ← IO.monoMsNow
    let mut busy := false
    match ← ch.tryRecv with
    | some ev =>
      busy := true
      match ← st.handle x ch notify ev now with
      | some st' => st := st'
      | none => return
    | none => pure ()
    if now ≥ st.lastTick + cfg.tickMs then
      let (n, e) ← st.node.onTick x now
      st ← ({ st with node := n, lastTick := now }).apply ch notify e
      for s in st.socks do
        if s.cid.isNone && s.heard + cfg.bareIdle < now then
          discard <| s.client.shutdown.block.toBaseIO
          st := st.drop s.id
    unless busy do IO.sleep 5

end

/-- A running node. -/
structure Runner where
  events : Std.Channel Event
  port : UInt16
  done : Task (Except IO.Error Unit)

/-- Listen on `port` (0: any) and run the node. -/
def Runner.start {F : Type} [Codec F] [SortKey F] (x : Sync F) (node : Node) (port : UInt16)
    (notify : List Id → IO Unit := fun _ => pure ()) (cfg : RunConfig := {}) : IO Runner := do
  let ch ← Std.Channel.new
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  srv.listen 16
  let bound := match ← srv.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let _ ← IO.asTask (prio := .dedicated) (acceptor ch srv)
  let done ← IO.asTask (prio := .dedicated) (runLoop x ch notify cfg { node })
  return { events := ch, port := bound, done }

/-- The app's own writes. -/
def Runner.write (r : Runner) (ops : List Op) : IO Unit := discard <| r.events.trySend (.write ops)

def Runner.stop (r : Runner) : IO Unit := discard <| r.events.trySend .stop

end Engine.Sync
