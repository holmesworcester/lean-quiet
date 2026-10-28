/-
The TCP runner: the one loop a phone app or a desktop daemon runs, so
neither carries socket code.

- It listens on a port and dials the bare addresses ("a.b.c.d:port")
  the node sends to; frames queue until the dial completes.
- Every payload is framed (`frame`, `unframe`: a 4-byte length, at most
  1 MiB; a longer one closes the socket).
- Every payload goes to the node's `onFrame` with its socket's address:
  sockets are not bound to sessions (a sealed frame names its own). An
  accepted socket's address is its peer's "ip:port", so a reply to that
  address goes back on the same socket.
- A socket silent for `idle` ms is closed: a join request waiting for
  approval is resent every tick, and sessions exchange rounds, so a
  live one is never idle that long.
- The app's writes come in through `Runner.write`; every id the node
  stores goes to the app's `notify`.

One task owns the node and its SQLite connection; the listener and one
reader per socket feed it events through a channel.

Every socket wait (`awaitUv`) blocks its own dedicated thread on the
socket's promise. It never goes through `Async.block`, which runs each
operation, and maps each result, as a task on the shared pool: when the
pool is busy (a phone decoding photos on every worker), every read,
send and dial would wait behind that work, and sync would crawl.
-/
import engine.wire.Node
import engine.wire.Frame
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

/-- Wait for a socket operation's promise on this thread, with no task
on the shared pool. -/
def awaitUv {α : Type} (op : IO (IO.Promise (Except IO.Error α))) : IO (Except IO.Error α) := do
  match ← op.toBaseIO with
  | .error e => pure (.error e)
  | .ok p =>
    match ← IO.wait p.result? with
    | some r => pure r
    | none => pure (.error (.userError "the socket's promise was dropped"))

structure Sock where
  id : Nat
  client : TCP.Socket.Client
  addr : ByteArray
  heard : Nat

structure RunState where
  db : Db
  node : Node
  socks : List Sock := []
  next : Nat := 0
  /-- Frames waiting for a dial to complete, by address. -/
  pending : List (ByteArray × List ByteArray) := []
  lastTick : Nat := 0

structure RunConfig where
  tickMs : Nat := 200
  idle : Nat := 600000

/-- Read frames from a socket into the channel until it closes. Each
read goes through `frames`, so what is kept between reads is less than
one maximal frame and its length (`buffer_bounded`). -/
def reader (ch : Std.Channel Event) (sid : Nat) (c : TCP.Socket.Client) : IO Unit := do
  let mut buf := ByteArray.empty
  repeat
    match ← awaitUv (c.native.recv? 65536) with
    | .ok (some chunk) =>
      let (ps, kept) := frames (buf ++ chunk)
      for p in ps do
        discard <| ch.trySend (.frame sid p)
      match kept with
      | some k => buf := k
      | none =>
        discard <| ch.trySend (.closed sid)
        return
    | _ =>
      discard <| ch.trySend (.closed sid)
      return

/-- Accept connections into the channel until stopped; then return, so
the listener is released and its port is free again. -/
def acceptor (ch : Std.Channel Event) (srv : TCP.Socket.Server) (stopped : IO.Ref Bool) : IO Unit := do
  repeat
    if ← stopped.get then return
    match ← srv.tryAccept.toBaseIO with
    | .ok (some c) =>
      let peer := match ← c.getPeerName.toBaseIO with
        | .ok a => addrText a
        | .error _ => "?"
      discard <| ch.trySend (.accepted c peer.toUTF8)
    | .ok none => IO.sleep 20
    | .error _ => IO.sleep 100

/-- Dial an address; the outcome goes into the channel. -/
def dialOut (ch : Std.Channel Event) (addr : ByteArray) : IO Unit := do
  match String.fromUTF8? addr >>= parseAddr with
  | none => discard <| ch.trySend (.dialed addr none)
  | some sa =>
    match ← TCP.Socket.Client.mk.toBaseIO with
    | .error _ => discard <| ch.trySend (.dialed addr none)
    | .ok c =>
      match ← awaitUv (c.native.connect sa) with
      | .ok _ => discard <| ch.trySend (.dialed addr (some c))
      | .error _ => discard <| ch.trySend (.dialed addr none)

def sendOn (c : TCP.Socket.Client) (payload : ByteArray) : IO Bool := do
  match ← awaitUv (c.native.send #[frame payload]) with
  | .ok _ => return true
  | .error _ => return false

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (ch : Std.Channel Event)
  (notify : List Id → IO Unit)

def RunState.sockOf (st : RunState) (p : Sock → Bool) : Option Sock := st.socks.find? p

def RunState.drop (st : RunState) (sid : Nat) : RunState :=
  { st with socks := st.socks.filter (·.id != sid) }

def RunState.addSock (st : RunState) (c : TCP.Socket.Client) (addr : ByteArray) (now : Nat) :
    IO (RunState × Nat) := do
  let sid := st.next
  let _ ← IO.asTask (prio := .dedicated) (reader ch sid c)
  return ({ st with socks := { id := sid, client := c, addr, heard := now } :: st.socks, next := sid + 1 }, sid)

/-- Carry out what the node asked for: send each payload to its
address, dialing if no socket has it. -/
def RunState.apply (st : RunState) (e : Effects) : IO RunState := do
  let mut st := st
  for (addr, b) in e.send do
    match st.sockOf (fun s => s.addr == addr) with
    | some s => unless ← sendOn s.client b do st := st.drop s.id
    | none =>
      match st.pending.find? (·.1 == addr) with
      | some _ =>
        st := { st with pending := st.pending.map fun (a, fs) => if a == addr then (a, fs ++ [b]) else (a, fs) }
      | none =>
        st := { st with pending := (addr, [b]) :: st.pending }
        let _ ← IO.asTask (prio := .dedicated) (dialOut ch addr)
  unless e.stored.isEmpty do notify e.stored
  return st

/-- Run a node step on the store. -/
def RunState.node? (st : RunState) (f : Node → SqlM F (Node × Effects)) : IO (RunState × Effects) := do
  let (n, e) ← (f st.node).run st.db
  return ({ st with node := n }, e)

/-- Handle one event; none to stop. -/
def RunState.handle (st : RunState) (ev : Event) (now : Nat) : IO (Option RunState) := do
  match ev with
  | .stop => return none
  | .frame sid p =>
    match st.sockOf (·.id == sid) with
    | none => return some st
    | some s =>
      let st := { st with socks := st.socks.map fun (s' : Sock) => if s'.id == sid then { s' with heard := now } else s' }
      let (st, e) ← st.node? fun n => n.onFrame x s.addr p now
      some <$> st.apply ch notify e
  | .closed sid => return some (st.drop sid)
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
    let (st, e) ← st.node? fun n => n.onWrite x ops now
    some <$> st.apply ch notify e

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
      | none =>
        for s in st.socks do
          discard <| awaitUv s.client.native.shutdown
        return
    | none => pure ()
    if now ≥ st.lastTick + cfg.tickMs then
      let (st', e) ← ({ st with lastTick := now }).node? fun n => n.onTick x now
      st ← st'.apply ch notify e
      for s in st.socks do
        if s.heard + cfg.idle < now then
          discard <| awaitUv s.client.native.shutdown
          st := st.drop s.id
    unless busy do IO.sleep 5

end

/-- A running node. -/
structure Runner where
  events : Std.Channel Event
  port : UInt16
  done : Task (Except IO.Error Unit)
  stopped : IO.Ref Bool
  listening : Task (Except IO.Error Unit)

/-- Listen on `port` (0: any) and run a node on this store, keeping
what is from `floor` on (0: everything). -/
def Runner.start {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (db : Db) (floor : Nat)
    (port : UInt16) (notify : List Id → IO Unit := fun _ => pure ()) (cfg : RunConfig := {}) :
    IO Runner := do
  let node := Node.boot x.fam (← (dumpOps (F := F)).run db) floor
  let ch ← Std.Channel.new
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  srv.listen 16
  let bound := match ← srv.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let stopped ← IO.mkRef false
  let listening ← IO.asTask (prio := .dedicated) (acceptor ch srv stopped)
  let done ← IO.asTask (prio := .dedicated) (runLoop x ch notify cfg { db, node })
  return { events := ch, port := bound, done, stopped, listening }

/-- The app's own writes. -/
def Runner.write (r : Runner) (ops : List Op) : IO Unit := discard <| r.events.trySend (.write ops)

/-- Stop: the loop ends and shuts every socket down, the listener is
released (its port free for the next start), and both are waited for. -/
def Runner.stop (r : Runner) : IO Unit := do
  r.stopped.set true
  discard <| r.events.trySend .stop
  discard <| IO.wait r.done
  discard <| IO.wait r.listening

end Engine.Sync
