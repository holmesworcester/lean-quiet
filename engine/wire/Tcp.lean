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
import engine.wire.Slots
import Std.Async.TCP
import Std.Sync.Channel

namespace Engine.Sync
open Std Std.Async Std.Net

/-- "a.b.c.d:port". -/
def addrText : SocketAddress → String
  | .v4 a => s!"{".".intercalate (a.addr.octets.toList.map (toString ·.toNat))}:{a.port}"
  | .v6 a => s!"[{a.addr}]:{a.port}"

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

def eventChannel (cfg : RunConfig) : IO (Std.CloseableChannel.Sync Event) :=
  Std.CloseableChannel.Sync.new (some cfg.queue)

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
  stopped : IO.Ref Bool

structure RunState where
  db : Db
  node : Node
  socks : List Sock := []
  next : Nat := 0
  /-- Frames waiting for a dial to complete, by address. -/
  pending : List (ByteArray × List ByteArray) := []
  lastTick : Nat := 0
  slots : Slots

/-- Block on a full event queue. Closing it releases stopped producers. -/
def enqueue (ch : Std.CloseableChannel.Sync Event) (ev : Event) : IO Bool := do
  return (← (ch.send ev).toBaseIO).isOk

/-- Cancel the read as well as shutting down writes, so its dedicated
reader releases its socket reference even if the peer never sends FIN. -/
def closeSocket (c : TCP.Socket.Client) : IO Unit := do
  discard <| c.native.cancelRecv.toBaseIO
  discard <| awaitUv c.native.shutdown

/-- A cancellable read, including a close racing the start of recv.
The promise is polled on this dedicated reader, never on the task pool. -/
def readSocket (c : TCP.Socket.Client) (stopped : IO.Ref Bool) (need : Nat) : IO (Option ByteArray) := do
  if ← stopped.get then return none
  let .ok p ← (c.native.recv? need.toUInt64).toBaseIO | return none
  repeat
    if ← stopped.get then
      discard <| c.native.cancelRecv.toBaseIO
      return none
    if ← p.isResolved then
      match ← IO.wait p.result? with
      | some (.ok chunk) => return chunk
      | _ => return none
    IO.sleep 1

/-- Read frames from a socket into the channel until it closes. Each
read goes through `frames`, so what is kept between reads is less than
one maximal frame and its length (`buffer_bounded`). -/
def reader (ch : Std.CloseableChannel.Sync Event) (sid : Nat) (c : TCP.Socket.Client) (stopped : IO.Ref Bool) : IO Unit := do
  let mut buf := ByteArray.empty
  repeat
    let need := if buf.size < 4 then 4 - buf.size
      else min 65536 ((lenAt buf).getD 0 + 4 - buf.size)
    match ← readSocket c stopped need with
    | some chunk =>
      let (ps, kept) := frames (buf ++ chunk)
      for p in ps do
        unless ← enqueue ch (.frame sid p) do return
      match kept with
      | some rest => buf := rest
      | none =>
        discard <| enqueue ch (.closed sid)
        return
    | _ =>
      discard <| enqueue ch (.closed sid)
      return

/-- Accept connections into the channel until stopped; then return, so
the listener is released and its port is free again. -/
def acceptor (ch : Std.CloseableChannel.Sync Event) (srv : TCP.Socket.Server) (stopped : IO.Ref Bool) (slots : Slots) (cfg : RunConfig) : IO Unit := do
  repeat
    if ← stopped.get then return
    match ← srv.tryAccept.toBaseIO with
    | .ok (some c) =>
      let peer := match ← c.getPeerName.toBaseIO with
        | .ok a => addrText a
        | .error _ => "?"
      if ← slots.take cfg peer.toUTF8 then
        unless ← enqueue ch (.accepted c peer.toUTF8) do
          closeSocket c
          slots.release peer.toUTF8
      else closeSocket c
    | .ok none => IO.sleep 20
    | .error _ => IO.sleep 100

/-- Dial an address; the outcome goes into the channel. -/
def dialOut (ch : Std.CloseableChannel.Sync Event) (slots : Slots) (addr : ByteArray) : IO Unit := do
  match String.fromUTF8? addr >>= parseAddr with
  | none => discard <| enqueue ch (.dialed addr none)
  | some sa =>
    match ← TCP.Socket.Client.mk.toBaseIO with
    | .error _ => discard <| enqueue ch (.dialed addr none)
    | .ok c =>
      match ← awaitUv (c.native.connect sa) with
      | .ok _ =>
        unless ← enqueue ch (.dialed addr (some c)) do
          closeSocket c
          slots.release addr
      | .error _ =>
        closeSocket c
        discard <| enqueue ch (.dialed addr none)

def sendOn (c : TCP.Socket.Client) (payload : ByteArray) : IO Bool := do
  match ← awaitUv (c.native.send #[frame payload]) with
  | .ok _ => return true
  | .error _ => return false

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (ch : Std.CloseableChannel.Sync Event)
  (notify : List Id → IO Unit)

def RunState.sockOf (st : RunState) (p : Sock → Bool) : Option Sock := st.socks.find? p

def RunState.drop (st : RunState) (sid : Nat) : RunState :=
  { st with socks := st.socks.filter (·.id != sid) }

def RunState.addSock (st : RunState) (c : TCP.Socket.Client) (addr : ByteArray) (now : Nat) :
    IO (RunState × Nat) := do
  let sid := st.next
  let stopped ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) (reader ch sid c stopped)
  return ({ st with socks := { id := sid, client := c, addr, heard := now, stopped } :: st.socks, next := sid + 1 }, sid)

/-- Every socket end notifies the node before releasing the socket. -/
def RunState.close (st : RunState) (sid now : Nat) : IO (RunState × Effects) := do
  match st.sockOf (·.id == sid) with
  | none => return (st, {})
  | some s =>
    let (node, e) ← (st.node.onClose x s.addr now).run st.db
    s.stopped.set true
    closeSocket s.client
    st.slots.release s.addr
    return ({ st.drop sid with node }, e)

/-- Carry out what the node asked for: send each payload to its
address, dialing if no socket has it; then close the sockets of the
sessions it dropped. -/
partial def RunState.apply (cfg : RunConfig) (st : RunState) (e : Effects) (now : Nat) : IO RunState := do
  let close (st : RunState) (sid : Nat) : IO RunState := do
    let (st, more) ← st.close x sid now
    st.apply cfg more now
  let mut st := st
  for (addr, b) in e.send do
    match st.sockOf (fun s => s.addr == addr) with
    | some s => unless ← sendOn s.client b do st ← close st s.id
    | none =>
      match st.pending.find? (·.1 == addr) with
      | some (_, fs) =>
        if fs.length < cfg.queue then
          st := { st with pending := st.pending.map fun (a, fs) => if a == addr then (a, fs ++ [b]) else (a, fs) }
        else
          let (node, more) ← (st.node.onClose x addr now).run st.db
          st ← ({ st with node, pending := st.pending.map fun (a, fs) => if a == addr then (a, []) else (a, fs) }).apply cfg more now
      | none =>
        if ← st.slots.take cfg addr then
          st := { st with pending := (addr, [b]) :: st.pending }
          let _ ← IO.asTask (prio := .dedicated) (dialOut ch st.slots addr)
  -- Then the dropped sessions' sockets close, after their last frames
  -- (a removed member's notice) are sent on them.
  for cid in e.drop do
    if let some addr := st.node.addr? cid then
      -- A socket may carry several sessions (a join sent beside an open
      -- one, until one is retired): close it once none is left on it.
      -- A dropped session is already out of `conns` (Node.drop).
      unless st.node.conns.any fun (c, _) => st.node.addr? c == some addr do
        for s in st.socks do
          if s.addr == addr then st ← close st s.id
  unless e.stored.isEmpty do notify e.stored
  unless e.purged.isEmpty do notify e.purged
  return st

/-- Run a node step on the store. -/
def RunState.node? (st : RunState) (f : Node → SqlM F (Node × Effects)) : IO (RunState × Effects) := do
  let (n, e) ← (f st.node).run st.db
  return ({ st with node := n }, e)

/-- A close can also produce couriers or new sessions; carry those
returned effects instead of losing them when the socket disappears. -/
def RunState.finishClose (cfg : RunConfig) (r : RunState × Effects) (now : Nat) : IO RunState :=
  r.1.apply x ch notify cfg r.2 now

def RunState.closeApply (cfg : RunConfig) (st : RunState) (sid now : Nat) : IO RunState := do
  RunState.finishClose x ch notify cfg (← st.close x sid now) now

/-- Handle one event; none to stop. -/
def RunState.handle (cfg : RunConfig) (st : RunState) (ev : Event) (now : Nat) : IO (Option RunState) := do
  match ev with
  | .stop => return none
  | .frame sid p =>
    match st.sockOf (·.id == sid) with
    | none => return some st
    | some s =>
      let st := { st with socks := st.socks.map fun (s' : Sock) => if s'.id == sid then { s' with heard := now } else s' }
      let (st, e) ← st.node? fun n => n.onFrame x s.addr p now
      some <$> st.apply x ch notify cfg e now
  | .closed sid => return some (← st.closeApply x ch notify cfg sid now)
  | .accepted c peer => return some (← st.addSock ch c peer now).1
  | .dialed addr none =>
    st.slots.release addr
    let (node, e) ← (st.node.onClose x addr now).run st.db
    some <$> ({ st with node, pending := st.pending.filter (·.1 != addr) }).apply x ch notify cfg e now
  | .dialed addr (some c) =>
    let (st, sid) ← st.addSock ch c addr now
    let frames := (st.pending.find? (·.1 == addr)).map (·.2) |>.getD []
    let mut st := { st with pending := st.pending.filter (·.1 != addr) }
    for b in frames do
      if let some s := st.sockOf (·.id == sid) then
        unless ← sendOn s.client b do st ← st.closeApply x ch notify cfg sid now
    return some st
  | .write ops =>
    let (st, e) ← st.node? fun n => n.onWrite x ops now
    some <$> st.apply x ch notify cfg e now

/-- The loop: events as they come, the clock every `tickMs`. -/
def runLoop (cfg : RunConfig) (st : RunState) : IO Unit := do
  let mut st := st
  repeat
    let now ← IO.monoMsNow
    let mut busy := false
    match ← ch.tryRecv with
    | some ev =>
      busy := true
      match ← st.handle x ch notify cfg ev now with
      | some st' => st := st'
      | none =>
        discard <| ch.close.toBaseIO
        for s in st.socks do
          st := (← st.close x s.id now).1
        for (_, addr) in st.node.addrs do
          let (node, _) ← (st.node.onClose x addr now).run st.db
          st := { st with node }
        return
    | none => pure ()
    if now ≥ st.lastTick + cfg.tickMs then
      let (st', e) ← ({ st with lastTick := now }).node? fun n => n.onTick x now
      st ← st'.apply x ch notify cfg e now
      for s in st.socks do
        if s.heard + cfg.idle < now then
          st ← st.closeApply x ch notify cfg s.id now
    unless busy do IO.sleep 5

end

/-- A running node. -/
structure Runner where
  events : Std.CloseableChannel.Sync Event
  port : UInt16
  done : Task (Except IO.Error Unit)
  stopped : IO.Ref Bool
  listening : Task (Except IO.Error Unit)
  slots : Slots

/-- Listen on `port` (0: any) and run a node on this store, keeping
what is from `floor` on (0: everything). -/
def Runner.start {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (db : Db) (floor : Nat)
    (port : UInt16) (notify : List Id → IO Unit := fun _ => pure ()) (cfg : RunConfig := {}) :
    IO Runner := do
  let node := Node.boot x.fam (← (dumpOps (F := F)).run db) floor
  let ch ← eventChannel cfg
  let slots ← Std.Mutex.new []
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  srv.listen 16
  let bound := match ← srv.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let stopped ← IO.mkRef false
  let listening ← IO.asTask (prio := .dedicated) (acceptor ch srv stopped slots cfg)
  let done ← IO.asTask (prio := .dedicated) (runLoop x ch notify cfg { db, node, slots })
  return { events := ch, port := bound, done, stopped, listening, slots }

/-- The app's own writes. -/
def Runner.write (r : Runner) (ops : List Op) : IO Unit := discard <| enqueue r.events (.write ops)

/-- Stop: the loop ends and shuts every socket down, the listener is
released (its port free for the next start), and both are waited for. -/
def Runner.stop (r : Runner) : IO Unit := do
  r.stopped.set true
  discard <| enqueue r.events .stop
  discard <| IO.wait r.done
  discard <| IO.wait r.listening
  while let some ev ← r.events.tryRecv do
    match ev with
    | .accepted c addr | .dialed addr (some c) =>
      closeSocket c
      r.slots.release addr
    | _ => pure ()

end Engine.Sync
