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
- The app's writes come in through `Runner.write`, on a channel of
  their own; three turns prefer local writes, then one turn guarantees
  network service (`Inbox.Priority.next`), falling back immediately when
  the preferred queue is empty. Every
  id the node stores goes to the app's `notify`.
- Each socket has a dedicated writer. Its actual `Outbox.take` calls the
  proved reservation core: local urgent frames first, protected controls,
  one catalog retry, then an ordinary serve burst. Normal and control
  queues each have byte/frame-count caps; the retry has one maxFrame slot.
  Ordinary overflow preserves the socket and its reserved work. Protected
  control overflow remains an explicit transport failure.
- On supported POSIX targets, the writer owns its native-send deadline,
  aborts both socket directions safely, and waits for the original SDK
  promise/callback to finish before releasing its slot. This also applies
  after retirement removes it from the loop's socket list. Windows retains
  the existing graceful wait without a claimed cancellation bound.
- Retry cursor progress is durable only after the actual writer completes
  the send. Queueing output alone cannot skip a catalog position.

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
import engine.wire.DialQueue
import engine.wire.Loop
import Std.Async.TCP
import Std.Sync.Channel
import engine.wire.Listener
import engine.wire.SocketAbort
import engine.wire.Reserved

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
  /-- Each socket's address and the bytes its lanes hold (`Runner.lanes`). -/
  | lanes (reply : IO.Promise (List (ByteArray × Nat)))
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

/-- What a socket's writer takes from: its lanes, and whether to stop. -/
structure Outbox where
  lanes : Lanes := {}
  /-- Bare handshakes and removal notices do not compete with ordinary data. -/
  control : Lanes := {}
  retry : RetrySlot RetryTicket := .vacant
  dropped : UInt64 := 0
  stopped : Bool := false
  /-- Finish queued frames before closing a retired session. -/
  draining : Bool := false
  /-- When the writer's write under way began; none between writes. -/
  since : Option Nat := none

/-- The writer's proved queue core: local urgent traffic stays first,
critical control follows, then one reserved retry and the normal burst. -/
def Outbox.queued (o : Outbox) : Reserved RetryTicket :=
  { ordinary := {
      urgent := o.lanes.urgent ++ o.control.urgent ++ o.control.serve
      serve := o.lanes.serve }, retry := o.retry }

def Outbox.ready (o : Outbox) : Bool := o.queued.ready

def Outbox.take (burst : Nat) (o : Outbox) : List ByteArray × Bool × Outbox :=
  let (frames, usedRetry, q) := o.queued.take burst
  (frames, usedRetry, { o with lanes := q.ordinary, control := {}, retry := q.retry })

/-- Ordinary overflow loses only repairable sync optimization traffic.
Protected-control overflow remains an explicit transport failure. -/
def Outbox.push (cfg : RunConfig) (critical : Bool) (o : Outbox)
    (ps : List (Lane × ByteArray)) : Bool × Outbox :=
  let q : Reserved RetryTicket := {
    ordinary := if critical then o.control else o.lanes
    retry := o.retry }
  let (ok, q') := q.push cfg.sockCap cfg.sockFrames ps
  if critical then
    (ok, { o with control := q'.ordinary })
  else
    (true, { o with lanes := q'.ordinary, dropped := if ok then o.dropped else o.dropped + 1 })

structure Sock where
  id : Nat
  client : TCP.Socket.Client
  addr : ByteArray
  heard : Nat
  stopped : IO.Ref Bool
  out : Std.Mutex Outbox
  wake : Std.Condvar
  /-- The writer: done once it has shut the socket down, or its write
  failed. -/
  done : Task (Except IO.Error Unit)
  aborter : Option SocketAbort := none

/-- Push frames and wake the writer. Ordinary overflow is repairable loss;
only protected-control refusal returns false and requests transport close.
Neither path can overwrite a reserved retry. -/
def Sock.push (cfg : RunConfig) (s : Sock) (ps : List (Lane × ByteArray))
    (critical : Bool := false) : IO Bool := do
  let ok ← s.out.atomically (modifyGetThe Outbox fun o => o.push cfg critical ps)
  s.wake.notifyAll
  return ok

def Sock.lanes (s : Sock) : IO Lanes := s.out.atomically do
  let o ← getThe Outbox
  return { o.queued.ordinary with serve := o.retry.take.1.toList ++ o.lanes.serve }

def Sock.offerRetry (s : Sock) (ticket : RetryTicket) (payload : ByteArray) : IO Bool := do
  let ok ← s.out.atomically (modifyGetThe Outbox fun o =>
    let (ok, retry) := o.retry.offer maxFrame ticket payload
    (ok, { o with retry }))
  s.wake.notifyAll
  return ok

def Sock.since (s : Sock) : IO (Option Nat) := s.out.atomically do return (← getThe Outbox).since

/-- What a session at each address may have served now, as the node
reads it (`Sync.room`): `roomOf` the sockets' lanes. -/
def rooms (cfg : RunConfig) (socks : List Sock) : IO (ByteArray → Option Nat) := do
  let qs ← socks.mapM fun s => do return (s.addr, ← s.lanes)
  return roomOf cfg.window qs

def retryRooms (socks : List Sock) : IO (ByteArray → Option Nat) := do
  let qs ← socks.mapM fun s => do
    let room ← s.out.atomically do
      match (← getThe Outbox).retry with
      | .vacant => return maxFrame
      | _ => return 0
    return (s.addr, room)
  return fun a => some (((qs.find? (·.1 == a)).map Prod.snd).getD 0)

/-- Stop a socket's writer, and drop what its lanes hold: it shuts the
socket down once its write under way is done. -/
def Sock.stop (s : Sock) : IO Unit := do
  s.out.atomically (modify fun o => { o with stopped := true, lanes := {}, control := {}, retry := .vacant })
  s.wake.notifyAll

/-- A protocol retirement sends its final notice before closing. Transport
failures still use `stop`, which discards queued frames immediately. -/
def Sock.drain (s : Sock) : IO Unit := do
  s.out.atomically (modify fun o => { o with draining := true })
  s.wake.notifyAll

structure RunState where
  db : Db
  node : Node
  socks : List Sock := []
  next : Nat := 0
  /-- Frames waiting for a dial to complete, by address. -/
  pending : List (ByteArray × List ByteArray) := []
  /-- Pending destinations not yet given a native socket reservation. -/
  waiting : List ByteArray := []
  slots : Slots

/-- Block on a full event queue. The SDK does not release waiting producers
on close; producer cancellation is a separate outstanding obligation. -/
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
          SocketAbort.closeIdle c
          slots.release peer.toUTF8
      else SocketAbort.closeIdle c
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
          SocketAbort.closeIdle c
          slots.release addr
      | .error _ =>
        SocketAbort.closeIdle c
        discard <| enqueue ch (.dialed addr none)

def sendOn (c : TCP.Socket.Client) (payload : ByteArray) : IO Bool := do
  match ← awaitUv (c.native.send #[frame payload]) with
  | .ok _ => return true
  | .error _ => return false

/-- One native write, still a sequence of ordinary length-prefixed frames. -/
def sendMany (c : TCP.Socket.Client) (payloads : List ByteArray) : IO Bool := do
  match ← awaitUv (c.native.send (payloads.map frame).toArray) with
  | .ok _ => return true
  | .error _ => return false

/-- A socket's writer, on its own thread: each native write is the next
`Outbox.take` batch, marked with when it began, until it is
stopped (then it shuts the socket down) or a write fails (then the loop
hears the socket closed). Its end releases the socket's slot. -/
def writer (ch : Std.CloseableChannel.Sync Event) (slots : Slots) (sid : Nat) (c : TCP.Socket.Client)
    (addr : ByteArray) (out : Std.Mutex Outbox) (wake : Std.Condvar) (burst : Nat)
    (aborter : Option SocketAbort := none) (stallMs : Nat := 30000) : IO Unit := do
  try
    repeat
      let batch ← out.atomicallyOnce wake (do let o ← getThe Outbox; return o.stopped || o.draining || o.ready) do
        let now ← IO.monoMsNow
        modifyGetThe Outbox fun o =>
          if o.stopped || (o.draining && !o.ready) then (none, o) else
          let (b, usedRetry, o') := o.take burst
          (some (b, usedRetry), { o' with since := some now })
      match batch with
      | none =>
        match aborter with
        | some cap =>
          discard <| c.native.cancelRecv.toBaseIO
          discard <| cap.abort
        | none => closeSocket c
        return
      | some (b, usedRetry) =>
        let stopped := out.atomically do return (← getThe Outbox).stopped
        unless ← SocketAbort.awaitSend aborter stallMs stopped (c.native.send (b.map frame).toArray) do
          -- The loop also observes done; a saturated event channel cannot
          -- retain a writer's native lease after its send has completed.
          discard <| ch.trySend (.closed sid)
          return
        out.atomically (modify fun o => { o with
          since := none
          retry := if usedRetry then o.retry.sent true else o.retry })
  finally slots.release addr

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (ch : Std.CloseableChannel.Sync Event)
  (notify : List Id → IO Unit)

def RunState.sockOf (st : RunState) (p : Sock → Bool) : Option Sock := st.socks.find? p

def RunState.drop (st : RunState) (sid : Nat) : RunState :=
  { st with socks := st.socks.filter (·.id != sid) }

/-- Reserve deferred destinations in their original FIFO order under the
listener's mutex. Failed quota checks retain both position and frames. -/
def RunState.startPending (cfg : RunConfig) (st : RunState) : IO RunState := do
  let chosen ← st.slots.atomically do
    modifyGetThe (List String) fun occupied => DialQueue.reserve cfg occupied st.waiting
  for addr in chosen do
    let _ ← IO.asTask (prio := .dedicated) (dialOut ch st.slots addr)
  return { st with waiting := st.waiting.filter (!chosen.contains ·) }

def RunState.addSock (cfg : RunConfig) (st : RunState) (c : TCP.Socket.Client) (addr : ByteArray) (now : Nat) :
    IO (RunState × Nat) := do
  let sid := st.next
  let stopped ← IO.mkRef false
  let out ← Std.Mutex.new {}
  let wake ← Std.Condvar.new
  let aborter ← SocketAbort.capture c
  let _ ← IO.asTask (prio := .dedicated) (reader ch sid c stopped)
  let done ← IO.asTask (prio := .dedicated) (writer ch st.slots sid c addr out wake cfg.burst aborter cfg.stallMs)
  let s : Sock := { id := sid, client := c, addr, heard := now, stopped, out := out, wake := wake, done, aborter }
  return ({ st with socks := s :: st.socks, next := sid + 1 }, sid)

/-- Every socket end notifies the node, then stops the socket's reader
and writer; the writer releases its slot when it ends. -/
def RunState.close (st : RunState) (sid now : Nat) (drain : Bool := false) : IO (RunState × Effects) := do
  match st.sockOf (·.id == sid) with
  | none => return (st, {})
  | some s =>
    let (node, e) ← (st.node.step x (.close s.addr) now).run st.db
    s.stopped.set true
    if drain then s.drain else s.stop
    return ({ st.drop sid with node }, e)

/-- Carry out what the node asked for: push each frame onto the lanes of
the socket at its address (`framesFor`), dialing if no socket has it.
Normal overflow is dropped; protected-control overflow closes the socket.
Reserved retry admission is independent of both queues. -/
partial def RunState.apply (cfg : RunConfig) (st : RunState) (e : Effects) (now : Nat) : IO RunState := do
  let close (st : RunState) (sid : Nat) : IO RunState := do
    let (st, more) ← st.close x sid now
    st.apply cfg more now
  let closeDrain (st : RunState) (sid : Nat) : IO RunState := do
    let (st, more) ← st.close x sid now true
    st.apply cfg more now
  let mut st := st
  let retryCount := e.retry.length
  let frames := laned (e.send.take (e.send.length - retryCount)) (e.serve - retryCount)
  let reserved := (e.send.drop (e.send.length - retryCount)).zip e.retry
  let criticalAddrs := e.critical ++ e.drop.filterMap st.node.addr?
  let sockOf (st : RunState) (a : ByteArray) := (st.sockOf fun s => s.addr == a).map (·.id)
  let mut over : List Nat := []
  for s in st.socks do
    let ps := framesFor (sockOf st) s.id frames
    unless ps.isEmpty do
      let critical := ps.filter fun p => criticalAddrs.contains s.addr || p.2[0]? == some bareTag
      let ordinary := ps.filter fun p => !(criticalAddrs.contains s.addr || p.2[0]? == some bareTag)
      unless critical.isEmpty do
        unless ← s.push cfg critical true do over := s.id :: over
      unless ordinary.isEmpty do discard <| s.push cfg ordinary
    for ((a, payload), ticket) in reserved do
      if sockOf st a == some s.id then discard <| s.offerRetry ticket payload
  for (addr, _, b) in frames do
    match st.sockOf (fun s => s.addr == addr) with
    | some _ => pure ()
    | none =>
      match st.pending.find? (·.1 == addr) with
      | some (_, fs) =>
        if fs.length < cfg.queue then
          st := { st with pending := st.pending.map fun (a, fs) => if a == addr then (a, fs ++ [b]) else (a, fs) }
        else
          let (node, more) ← (st.node.step x (.close addr) now).run st.db
          st ← ({ st with node, pending := st.pending.map fun (a, fs) => if a == addr then (a, []) else (a, fs) }).apply cfg more now
      | none =>
        if st.pending.length < cfg.maxPending then
          st := { st with pending := st.pending ++ [(addr, [b])], waiting := DialQueue.enqueue cfg.maxPending addr st.waiting }
  st ← st.startPending ch cfg
  for sid in over do st ← close st sid
  -- Then the dropped sessions' sockets close, after their last frames
  -- (a removed member's notice) are sent on them.
  for cid in e.drop do
    if let some addr := st.node.addr? cid then
      -- A socket may carry several sessions (a join sent beside an open
      -- one, until one is retired): close it once none is left on it.
      -- A dropped session is already out of `conns` (Node.drop).
      unless st.node.conns.any fun (c, _) => st.node.addr? c == some addr do
        for s in st.socks do
          if s.addr == addr then st ← closeDrain st s.id
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

/-- A native writer's completion is authoritative even if its nonblocking
closed notification found the event queue full. Never wait for the task. -/
def RunState.reap (cfg : RunConfig) (st : RunState) (now : Nat) : IO RunState := do
  let mut st := st
  for s in st.socks do
    if ← IO.hasFinished s.done then st ← st.closeApply x ch notify cfg s.id now
  return st

/-- Handle one event; none to stop. -/
def RunState.handle (cfg : RunConfig) (st : RunState) (ev : Event) (now : Nat) : IO (Option RunState) := do
  match ev with
  | .stop => return none
  | .frame sid p =>
    match st.sockOf (·.id == sid) with
    | none => return some st
    | some s =>
      let st := { st with socks := st.socks.map fun (s' : Sock) => if s'.id == sid then { s' with heard := now } else s' }
      let x' := { x with room := ← rooms cfg st.socks }
      let (st, e) ← st.node? fun n => n.step x' (.frame s.addr p) now
      some <$> st.apply x ch notify cfg e now
  | .closed sid => return some (← st.closeApply x ch notify cfg sid now)
  | .lanes reply =>
    reply.resolve (← st.socks.mapM fun s => do return (s.addr, (← s.lanes).bytes))
    return some st
  | .accepted c peer => return some (← st.addSock ch cfg c peer now).1
  | .dialed addr none =>
    st.slots.release addr
    let (node, e) ← (st.node.step x (.close addr) now).run st.db
    some <$> ({ st with node, pending := st.pending.filter (·.1 != addr), waiting := st.waiting.filter (· != addr) }).apply x ch notify cfg e now
  | .dialed addr (some c) =>
    let (st, sid) ← st.addSock ch cfg c addr now
    let frames := (st.pending.find? (·.1 == addr)).map (·.2) |>.getD []
    let st := { st with pending := st.pending.filter (·.1 != addr), waiting := st.waiting.filter (· != addr) }
    -- A new address's first frames are the session's opening: urgent.
    if let some s := st.sockOf (·.id == sid) then
      unless ← s.push cfg (frames.map (.urgent, ·)) true do
        return some (← st.closeApply x ch notify cfg sid now)
    return some st

/-- Stop producers, notify the node of every remaining transport end and
wait at most `stopMs` for writes already under way. -/
def RunState.shutdown (cfg : RunConfig) (writes : Std.CloseableChannel.Sync (List Op))
    (st : RunState) (now : Nat) : IO RunState := do
  let mut st := st
  discard <| ch.close.toBaseIO
  discard <| writes.close.toBaseIO
  let socks := st.socks
  for s in socks do
    st := (← st.close x s.id now).1
  for (_, addr) in st.node.addrs do
    let (node, _) ← (st.node.step x (.close addr) now).run st.db
    st := { st with node }
  for s in socks do
    while !(← IO.hasFinished s.done) && (← IO.monoMsNow) < now + cfg.stopMs do
      IO.sleep 5
  return st

/-- Native writer completion is harvested before opening the next retry
slot. Metadata is written outside the socket mutex, by the loop alone. -/
def RunState.ackRetries (st : RunState) : IO Unit := do
  let some store := x.retryStore | return
  for s in st.socks do
    let done ← s.out.atomically do return (← getThe Outbox).retry.completed?
    if let some ticket := done then
      (store.commit ticket).run st.db
      s.out.atomically (modify fun o =>
        if o.retry.completed? = some ticket then { o with retry := o.retry.acknowledged } else o)

/-- Native adapters for the shared turn. Every node invocation uses
`Node.step`; frames, effects, socket expiry and shutdown retain their actual
SQLite and TCP implementations. -/
def RunState.loopBackend (cfg : RunConfig) (writes : Std.CloseableChannel.Sync (List Op)) :
    Loop.Backend IO RunState (List Op) Event where
  clock := IO.monoMsNow
  writes := writes.tryRecv
  events := ch.tryRecv
  write := fun st ops now => do
    let (st, e) ← st.node? fun n => n.step x (.write ops) now
    st.apply x ch notify cfg e now
  event := fun st ev now => st.handle x ch notify cfg ev now
  tick := fun st now => do
    st.ackRetries x
    let x' := { x with room := ← rooms cfg st.socks, retryRoom := ← retryRooms st.socks }
    let (st, e) ← st.node? fun n => n.step x' .tick now
    st.apply x ch notify cfg e now
  expire := fun st now => do
    let mut st ← st.reap x ch notify cfg now
    for s in st.socks do
      if shut cfg.idle cfg.stallMs now s.heard (← s.since) then
        st ← st.closeApply x ch notify cfg s.id now
    return st
  stop := fun st now => st.shutdown x ch cfg writes now
  idle := IO.sleep 5

/-- Fixed-width counters, rather than an ever-growing trace. -/
structure TurnCounters where
  started : UInt64 := 0
  completed : UInt64 := 0
  writes : UInt64 := 0
  events : UInt64 := 0
  ticks : UInt64 := 0
  deriving BEq, Repr

/-- Fixed-size telemetry written by the runner itself. No external observer
callback or growing history can block a turn. Counters wrap modulo 2^64. -/
def TurnCounters.record {W E : Type} (c : TurnCounters) (selected : Option (W ⊕ E))
    (ticked : Bool) : TurnCounters :=
  { c with
    completed := c.completed + 1
    writes := c.writes + (if selected.any (fun s => match s with | .inl _ => true | _ => false) then 1 else 0)
    events := c.events + (if selected.any (fun s => match s with | .inr _ => true | _ => false) then 1 else 0)
    ticks := c.ticks + (if ticked then 1 else 0) }

/-- Repeatedly execute the shared production turn, retaining its bounded
phase and recording completed work without an observer callback. -/
def runLoop (cfg : RunConfig) (writes : Std.CloseableChannel.Sync (List Op)) (st : RunState)
    (turns : IO.Ref TurnCounters) : IO Unit := do
  let backend := RunState.loopBackend x ch notify cfg writes
  let mut state : Loop.State RunState := { value := st }
  repeat
    turns.modify fun c => { c with started := c.started + 1 }
    let result ← Loop.turn backend cfg.tickMs state
    turns.modify fun c => c.record result.observed.selected result.ticked
    if result.stopped then return
    state := result.state

end

/-- A running node. -/
structure Runner where
  events : Std.CloseableChannel.Sync Event
  /-- Local writes have their own bounded channel and three preferred slots in four.
  App offers are nonblocking; a full queue leaves writes parked in App. -/
  writes : Std.CloseableChannel.Sync (List Op)
  port : UInt16
  done : Task (Except IO.Error Unit)
  stopped : IO.Ref Bool
  listening : Task (Except IO.Error Unit)
  slots : Slots
  listener : Std.Internal.UV.TCP.Socket
  closing : Std.Mutex Bool
  turnCounters : IO.Ref TurnCounters

/-- A nonblocking snapshot of fixed-size runner telemetry. `started` advances
before polling, so a notification emitted inside that turn can identify it. -/
def Runner.counters (r : Runner) : IO TurnCounters := r.turnCounters.get

/-- Listen on `port` (0: any) and run a node on this store, keeping
what is from `floor` on (0: everything). -/
def Runner.start {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (db : Db) (floor : Nat)
    (port : UInt16) (notify : List Id → IO Unit := fun _ => pure ()) (cfg : RunConfig := {}) :
    IO Runner := do
  let x := { x with catalog := some (Catalog.sql (F := F)), retryStore := some (RetryStore.sql (F := F)), deferredRetries := true }
  let node := Node.boot x.fam (← (dumpOps (F := F)).run db) floor
  let ch ← eventChannel cfg
  let writes ← Std.CloseableChannel.Sync.new (some cfg.queue)
  let slots ← Std.Mutex.new []
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  srv.listen 16
  let bound := match ← srv.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let stopped ← IO.mkRef false
  let listening ← IO.asTask (prio := .dedicated) (acceptor ch srv stopped slots cfg)
  let turnCounters ← IO.mkRef ({} : TurnCounters)
  let done ← IO.asTask (prio := .dedicated) do
    try runLoop x ch notify cfg writes { db, node, slots } turnCounters
    catch e =>
      -- The native shells retain stderr (iOS lean.log / Android logcat).
      -- A background IO failure must not disappear into an unread Task.
      IO.eprintln s!"network runner stopped: {e}"
      throw e
  let closing ← Std.Mutex.new false
  return { events := ch, writes, port := bound, done, stopped, listening, slots, listener := srv.native, closing, turnCounters }

/-- Each socket's address and the bytes its lanes hold now, in the
loop's turn; empty once it has stopped. -/
def Runner.lanes (r : Runner) : IO (List (ByteArray × Nat)) := do
  let p ← IO.Promise.new
  unless ← enqueue r.events (.lanes p) do return []
  return (← IO.wait p.result?).getD []

/-- Queue local writes for bounded-fair service. Background callers may wait
for space; the app uses `writes.trySend` and keeps unaccepted writes. -/
def Runner.write (r : Runner) (ops : List Op) : IO Unit := discard <| (r.writes.send ops).toBaseIO

/-- Stop: the loop ends and shuts every socket down, the listener is
released (its port free for the next start), and both are waited for. -/
def Runner.stop (r : Runner) : IO Unit := r.closing.atomically do
  if ← getThe Bool then return
  set true
  r.stopped.set true
  discard <| enqueue r.events .stop
  discard <| IO.wait r.done
  discard <| IO.wait r.listening
  closeListener r.listener
  while let some ev ← r.events.tryRecv do
    match ev with
    | .accepted c addr | .dialed addr (some c) =>
      -- These clients never reached addSock, so no reader/writer started.
      SocketAbort.closeIdle c
      r.slots.release addr
    | _ => pure ()

end Engine.Sync
