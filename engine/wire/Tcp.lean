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
- Silence expiry gives an already-admitted source one bounded selection
  opportunity before closing. Junk cannot refill the authenticated session
  budget; explicit retirement and stalled native writes bypass the grace.
  Join requests retry on ticks, and established sessions send keepalives.
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
import engine.wire.StopFlag
import engine.wire.Reserved
import engine.wire.IngressIO
import engine.wire.ExpiryGrace
import engine.wire.JobOwners

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
  stopped : StopFlag
  out : Std.Mutex Outbox
  wake : Std.Condvar
  /-- The writer: done after native send cleanup and its original reader
  task have completed. Native quota is retained until both jobs finish. -/
  done : Task (Except IO.Error Unit)
  readerDone : Task (Except IO.Error Unit) := Task.pure (.ok ())
  aborter : Option SocketAbort := none
  input : Option Ingress.Source := none
  /-- A transport close owes exactly its frozen, already-admitted frame. -/
  closeAfterFrame : Bool := false

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
  -- the reserved retry slot's offer (Reserved.offer: offer_bounded)
  let ok ← s.out.atomically (modifyGetThe Outbox fun o =>
    let (ok, q) := o.queued.offer maxFrame ticket payload
    (ok, { o with retry := q.retry }))
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

/-- Failure requests stop immediately without waiting for native callbacks.
A retiring notice retains its finite queue and the writer's existing deadline. -/
def Sock.cancelOwned (hub : Ingress.Hub Event) (s : Sock) : IO Unit := do
  s.stopped.request
  if let some input := s.input then hub.retire input
  s.out.atomically (modify fun o =>
    if o.draining then o else { o with stopped := true, lanes := {}, control := {}, retry := .vacant })
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
  ingress : Ingress.Hub Event
  /-- Original native jobs survive exceptions before whole-turn publication. -/
  owners : Option JobOwners := none
  /-- One finite grace per live authenticated heard generation. -/
  sessionGrace : List (Id × ExpiryGrace.State) := []
  /-- Socket idle grace is separate; native send stalls never consult it. -/
  socketGrace : List (Nat × ExpiryGrace.State) := []

/-- Backpressure retains one value on this producer's stack. Closing the
queue or requesting cancellation releases it without an SDK send waiter. -/
def enqueue (ch : Std.CloseableChannel.Sync Event) (ev : Event)
    (cancel : IO Bool := pure false) : IO Bool := do
  repeat
    if (← cancel) || (← ch.isClosed) then return false
    if ← ch.trySend ev then return true
    IO.sleep 1

/-- Cancel the read as well as shutting down writes, so its dedicated
reader releases its socket reference even if the peer never sends FIN. -/
def closeSocket (c : TCP.Socket.Client) : IO Unit := do
  discard <| c.native.cancelRecv.toBaseIO
  discard <| awaitUv c.native.shutdown

/-- A cancellable read, including a close racing the start of recv.
The promise is polled on this dedicated reader, never on the task pool. -/
def readSocket (c : TCP.Socket.Client) (stopped : StopFlag) (need : Nat) : IO (Option ByteArray) := do
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
def reader (hub : Ingress.Hub Event) (input : Ingress.Source) (sid : Nat)
    (c : TCP.Socket.Client) (stopped : StopFlag) : IO Unit := do
  let mut buf := ByteArray.empty
  repeat
    let need := if buf.size < 4 then 4 - buf.size
      else min 65536 ((lenAt buf).getD 0 + 4 - buf.size)
    match ← readSocket c stopped need with
    | some chunk =>
      let (ps, kept) := frames (buf ++ chunk)
      for p in ps do
        unless ← hub.send input (.frame sid p) stopped.get do return
      match kept with
      | some rest => buf := rest
      | none =>
        discard <| hub.send input (.closed sid) stopped.get
        return
    | _ =>
      discard <| hub.send input (.closed sid) stopped.get
      return

/-- Accept connections into the channel until stopped; then return, so
the listener is released and its port is free again. -/
def acceptor (ch : Std.CloseableChannel.Sync Event) (srv : TCP.Socket.Server) (stopped : StopFlag) (slots : Slots) (cfg : RunConfig)
    (cancel : IO Bool := pure false) : IO Unit := do
  let canceled := do return (← stopped.get) || (← cancel)
  repeat
    if ← canceled then return
    match ← srv.tryAccept.toBaseIO with
    | .ok (some c) =>
      let peer := match ← c.getPeerName.toBaseIO with
        | .ok a => addrText a
        | .error _ => "?"
      if ← slots.take cfg peer.toUTF8 then
        unless ← enqueue ch (.accepted c peer.toUTF8) canceled do
          SocketAbort.closeIdle c
          slots.release peer.toUTF8
      else SocketAbort.closeIdle c
    | .ok none => IO.sleep 20
    | .error _ => IO.sleep 100

/-- Dial an address; ownership of its reserved slot transfers with the
completion event. Supported POSIX sockets keep their original connect promise
until deadline/stop abort has completed its callback. Other targets retain
the ordinary wait. Refusing a completion releases the still-owned slot. -/
def dialOut (ch : Std.CloseableChannel.Sync Event) (slots : Slots) (addr : ByteArray)
    (cancel : IO Bool := pure false) (timeout : Nat := 30000) : IO Unit := do
  let failed : IO Unit := do
    unless ← enqueue ch (.dialed addr none) cancel do slots.release addr
  match String.fromUTF8? addr >>= parseAddr with
  | none => failed
  | some sa =>
    match ← TCP.Socket.Client.mk.toBaseIO with
    | .error _ => failed
    | .ok c =>
      let connected ← (do
        -- Binding creates the descriptor while the client is idle, so
        -- capture never races uv_fileno against an in-flight connect.
        c.bind (match sa with
          | .v4 _ => .v4 ⟨IPv4Addr.ofParts 0 0 0 0, 0⟩
          | .v6 _ => .v6 ⟨IPv6Addr.ofParts 0 0 0 0 0 0 0 0, 0⟩)
        let aborter ← SocketAbort.capture c
        SocketAbort.awaitSend aborter timeout cancel (c.native.connect sa)).toBaseIO
      match connected with
      | .ok true =>
        unless ← enqueue ch (.dialed addr (some c)) cancel do
          SocketAbort.closeIdle c
          slots.release addr
      | _ =>
        SocketAbort.closeIdle c
        failed

def sendOn (c : TCP.Socket.Client) (payload : ByteArray) : IO Bool := do
  match ← awaitUv (c.native.send #[frame payload]) with
  | .ok _ => return true
  | .error _ => return false

/-- One native write, still a sequence of ordinary length-prefixed frames. -/
def sendMany (c : TCP.Socket.Client) (payloads : List ByteArray) : IO Bool := do
  match ← awaitUv (c.native.send (payloads.map frame).toArray) with
  | .ok _ => return true
  | .error _ => return false

/-- Stop the original reader, including a full-mailbox retry or a recv
registration racing cancellation, then wait for that task to finish. SDK
cancelRecv drops its promise rather than resolving it: wait on the reader
task, never on that canceled recv promise. No socket/source mutex is held.
The main close/reap path retains ownership of the ingress source. -/
def finishReader (stopped : StopFlag) (client : TCP.Socket.Client)
    (job : Task (Except IO.Error Unit)) : IO Unit := do
  stopped.request
  discard <| client.native.cancelRecv.toBaseIO
  discard <| IO.wait job

/-- A retirement's end, once its final frames are written: a FIN, then
read and discard until the peer's own end, within `stallMs`. Shutting both
directions at once instead makes the peer's next write meet a reset, and a
peer whose write fails stops reading: the removal notice it has not yet
read is lost. The original reader is finished first, so this is the
socket's only read. -/
def linger (cap : SocketAbort) (c : TCP.Socket.Client) (stallMs : Nat)
    (finishReader : IO Unit) : IO Unit := do
  finishReader
  unless ← cap.finishWrite do return
  let deadline := (← IO.monoMsNow) + stallMs
  repeat
    let .ok p ← (c.native.recv? 65536).toBaseIO | return
    repeat
      if ← p.isResolved then break
      if (← IO.monoMsNow) ≥ deadline then
        discard <| c.native.cancelRecv.toBaseIO
        return
      IO.sleep 1
    match ← IO.wait p.result? with
    | some (.ok (some _)) => pure ()
    | _ => return

/-- A socket's writer, on its own thread: each native write is the next
`Outbox.take` batch, marked with when it began, until it is
stopped (then it shuts the socket down), drained (then it `linger`s first)
or a write fails (then the loop hears the socket closed). Its end releases
the socket's slot. -/
def writer (ch : Std.CloseableChannel.Sync Event) (slots : Slots) (sid : Nat) (c : TCP.Socket.Client)
    (addr : ByteArray) (out : Std.Mutex Outbox) (wake : Std.Condvar) (burst : Nat)
    (aborter : Option SocketAbort := none) (stallMs : Nat := 30000)
    (cleanupReader : IO Unit := pure ()) : IO Unit := do
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
          -- Not stopped, so a drain ended: a retirement, whose last frames
          -- the peer must still be able to read.
          unless ← out.atomically (do return (← getThe Outbox).stopped) do
            linger cap c stallMs cleanupReader
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
  finally
    cleanupReader
    slots.release addr

section
variable {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (ch : Std.CloseableChannel.Sync Event)
  (notify : List Id → IO Unit)

def RunState.sockOf (st : RunState) (p : Sock → Bool) : Option Sock := st.socks.find? p

def RunState.drop (st : RunState) (sid : Nat) : RunState :=
  { st with
    socks := st.socks.filter (·.id != sid)
    socketGrace := st.socketGrace.filter (·.1 != sid) }

/-- The real primary write/event dispatch consumes one unit per selection.
Producers and timer ticks cannot replenish this finite budget. -/
def RunState.selected (st : RunState) : RunState :=
  { st with
    sessionGrace := st.sessionGrace.map fun (cid, g) => (cid, ExpiryGrace.consume g)
    socketGrace := st.socketGrace.map fun (sid, g) => (sid, ExpiryGrace.consume g) }

/-- Silence expiry observes only the bounded, already-admitted mailboxes.
No payload is processed before the normal UI-first selector chooses it. -/
def RunState.prepareExpiry (cfg : RunConfig) (st : RunState) (now : Nat) : IO (RunState × List Id) := do
  let ready := (← st.ingress.pending).filterMap fun e => match e with
    | .frame sid _ => some sid
    | _ => none
  let readyAddresses := st.socks.filterMap fun s => if ready.contains s.id then some s.addr else none
  let closing := st.socks.filter (·.closeAfterFrame) |>.map (·.addr)
  let mut sessionGrace := []
  let mut deferred := []
  for (cid, c) in st.node.conns do
    let old := (st.sessionGrace.find? (·.1 == cid)).map Prod.snd
    let pending := (st.node.addr? cid).any readyAddresses.contains
    let (protect, next) := ExpiryGrace.check (ExpiryGrace.budget cfg.maxSocks) c.heard
      (Decidable.decide (c.heard + x.cfg.live < now)) pending old
    if let some g := next then sessionGrace := (cid, g) :: sessionGrace
    if protect || (st.node.addr? cid).any closing.contains then deferred := cid :: deferred
  let mut socketGrace := []
  for s in st.socks do
    let old := (st.socketGrace.find? (·.1 == s.id)).map Prod.snd
    let (_, next) := ExpiryGrace.check (ExpiryGrace.budget cfg.maxSocks) s.heard
      (Decidable.decide (s.heard + cfg.idle < now)) (ready.contains s.id) old
    if let some g := next then socketGrace := (s.id, g) :: socketGrace
  return ({ st with sessionGrace, socketGrace }, deferred)

/-- Reserve deferred destinations in their original FIFO order under the
listener's mutex. Failed quota checks retain both position and frames. -/
def RunState.startPending (cfg : RunConfig) (st : RunState) : IO RunState := do
  let chosen ← st.slots.atomically do
    modifyGetThe (List String) fun occupied => DialQueue.reserve cfg occupied st.waiting
  let mut launched := []
  for addr in chosen do
    let create : BaseIO (Unit × NativeJob) := do
      let done ← IO.asTask (prio := .dedicated) (dialOut ch st.slots addr st.ingress.stopped cfg.stallMs)
      return ((), ⟨pure (), done⟩)
    let admitted ← match st.owners with
      | some owners => Option.isSome <$> owners.launch create
      | none => do discard <| create; pure true
    if admitted then launched := addr :: launched
    else st.slots.release addr
  return { st with waiting := st.waiting.filter (!launched.contains ·) }

def RunState.addSock (cfg : RunConfig) (st : RunState) (c : TCP.Socket.Client) (addr : ByteArray) (now : Nat) :
    IO (RunState × Option Nat) := do
  let some input ← st.ingress.reserve | do
    SocketAbort.closeIdle c
    st.slots.release addr
    return (st, none)
  let sid := st.next
  -- All fallible setup precedes task creation. A refused owner slot still
  -- owns an idle client and can release it without leaving a native worker.
  let setup ← (do
    let stopped ← StopFlag.new
    let out ← Std.Mutex.new ({} : Outbox)
    let wake ← Std.Condvar.new
    let aborter ← SocketAbort.capture c
    return (stopped, out, wake, aborter)).toBaseIO
  let .ok (stopped, out, wake, aborter) := setup | do
    st.ingress.retire input
    SocketAbort.closeIdle c
    st.slots.release addr
    match setup with | .error e => throw e | _ => return (st, none)
  let create : BaseIO (Sock × NativeJob) := do
    let readerDone ← IO.asTask (prio := .dedicated) (reader st.ingress input sid c stopped)
    let done ← IO.asTask (prio := .dedicated)
      (writer ch st.slots sid c addr out wake cfg.burst aborter cfg.stallMs
        (finishReader stopped c readerDone))
    let s : Sock := {
      id := sid, client := c, addr, heard := now, stopped, out, wake
      done, readerDone, aborter, input := some input }
    return (s, ⟨s.cancelOwned st.ingress, done⟩)
  let socket ← match st.owners with
    | some owners => owners.launch create
    | none => (fun result => some result.1) <$> create
  let some s := socket | do
    st.ingress.retire input
    SocketAbort.closeIdle c
    st.slots.release addr
    return (st, none)
  return ({ st with socks := s :: st.socks, next := sid + 1 }, some sid)

/-- Every socket end notifies the node, then stops the socket's reader
and writer; the writer releases its slot when it ends. -/
def RunState.close (st : RunState) (sid now : Nat) (drain : Bool := false) : IO (RunState × Effects) := do
  match st.sockOf (·.id == sid) with
  | none => return (st, {})
  | some s =>
    let (node, e) ← (st.node.step x (.close s.addr) now).run st.db
    s.stopped.request
    if let some input := s.input then st.ingress.retire input
    if drain then s.drain else s.stop
    return ({ st.drop sid with
      node
      sessionGrace := st.sessionGrace.filter fun (cid, _) => node.conns.any (·.1 == cid) }, e)

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

/-- A transport failure cannot overtake its source's already admitted
frame. Freeze under the producer mutex, retain one one-shot obligation, and
stop future I/O; explicit protocol retirement/shutdown still closes directly.
Repeated control/reap observations cannot renew or replace the saved frame. -/
def RunState.transportClosed (cfg : RunConfig) (st : RunState) (sid now : Nat) : IO RunState := do
  let some s := st.sockOf (·.id == sid) | return st
  if s.closeAfterFrame then return st
  s.stopped.request
  let pending ← match s.input with
    | some source => st.ingress.freeze source
    | none => pure none
  s.stop
  match pending with
  | some (.frame source _) =>
    if source == sid then
      return { st with socks := st.socks.map fun sock =>
        if sock.id == sid then { sock with closeAfterFrame := true } else sock }
    else st.closeApply x ch notify cfg sid now
  | _ => st.closeApply x ch notify cfg sid now

/-- A finished writer still owes its one frozen admitted input, if any.
Never wait for a native task or allow new input to replenish that obligation. -/
def RunState.reap (cfg : RunConfig) (st : RunState) (now : Nat) : IO RunState := do
  let mut st := st
  for s in st.socks do
    if ← IO.hasFinished s.done then st ← st.transportClosed x ch notify cfg s.id now
  return st

/-- A selected frozen frame can fail after leaving its mailbox. Retire its
native ownership even if the store also rejects close-time writes; preserve
the original handler error for the caller. Durable erasure cannot be promised
while SQLite refuses writes. Ordinary successful retirement is unchanged. -/
def RunState.failedFrame (cfg : RunConfig) (st : RunState) (s : Sock) (now : Nat) : IO Unit := do
  s.stopped.request
  if let some input := s.input then st.ingress.retire input
  s.stop
  try discard <| st.closeApply x ch notify cfg s.id now
  catch _ => pure ()

/-- Handle one event; none to stop. -/
def RunState.handle (cfg : RunConfig) (st : RunState) (ev : Event) (now : Nat) : IO (Option RunState) := do
  match ev with
  | .stop => return none
  | .frame sid p =>
    match st.sockOf (·.id == sid) with
    | none => return some st
    | some s =>
      try
        let st := { st with socks := st.socks.map fun (s' : Sock) => if s'.id == sid then { s' with heard := now } else s' }
        let x' := { x with room := ← rooms cfg st.socks }
        let (st, e) ← st.node? fun n => n.step x' (.frame s.addr p) now
        let st ← st.apply x ch notify cfg e now
        -- Selection consumes the one frozen obligation even when authentication
        -- or decoding refused its contents. No second frame can rearm it.
        if s.closeAfterFrame then return some (← st.closeApply x ch notify cfg sid now)
        return some st
      catch error =>
        if s.closeAfterFrame then st.failedFrame x ch notify cfg s now
        throw error
  | .closed sid => return some (← st.transportClosed x ch notify cfg sid now)
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
    let some sid := sid | do
      let (node, e) ← (st.node.step x (.close addr) now).run st.db
      return some (← ({ st with
        node
        pending := st.pending.filter (·.1 != addr)
        waiting := st.waiting.filter (· != addr) }).apply x ch notify cfg e now)
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
  st.ingress.stop
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
def RunState.loopBackend (cfg : RunConfig) (writes : Std.CloseableChannel.Sync (List Op))
    (ingress : Ingress.Hub Event) :
    Loop.Backend IO RunState (List Op) Event where
  clock := IO.monoMsNow
  writes := writes.tryRecv
  events := do
    if ← ingress.stopped then return some .stop
    ingress.poll ch.tryRecv
  write := fun st ops now => do
    let st := st.selected
    let (st, e) ← st.node? fun n => n.step x (.write ops) now
    st.apply x ch notify cfg e now
  event := fun st ev now => st.selected.handle x ch notify cfg ev now
  tick := fun st now => do
    let (st, deferred) ← st.prepareExpiry x cfg now
    st.ackRetries x
    let x' := { x with
      room := ← rooms cfg st.socks
      retryRoom := ← retryRooms st.socks
      tickReady := fun cid => !deferred.contains cid && x.tickReady cid }
    let (st, e) ← st.node? fun n => n.step x' .tick now
    st.apply x ch notify cfg e now
  expire := fun st now => do
    let mut st ← st.reap x ch notify cfg now
    let ready := (← st.ingress.pending).filterMap fun e => match e with
      | .frame sid _ => some sid
      | _ => none
    for s in st.socks do
      if s.closeAfterFrame then continue
      let grace := (st.socketGrace.find? (·.1 == s.id)).any fun (_, g) =>
        g.heard == s.heard && g.left != 0 && ready.contains s.id
      let since ← s.since
      let stalled := since.any fun start => start + cfg.stallMs ≤ now
      if stalled || (!grace && shut cfg.idle cfg.stallMs now s.heard since) then
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
  let backend := RunState.loopBackend x ch notify cfg writes st.ingress
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
  stopped : StopFlag
  listening : Task (Except IO.Error Unit)
  slots : Slots
  listener : Std.Internal.UV.TCP.Socket
  closing : Std.Mutex Bool
  turnCounters : IO.Ref TurnCounters
  ingress : Ingress.Hub Event
  owners : Option JobOwners := none
  cleanup : Option (Task (Except IO.Error Unit)) := none

/-- A snapshot of fixed-size runner telemetry. `started` advances
before polling, so a notification emitted inside that turn can identify it. -/
def Runner.counters (r : Runner) : IO TurnCounters := r.turnCounters.get

/-- Join native producers before reclaiming their unadmitted clients. This
fixed owned task runs after loop completion even if no caller invokes stop. -/
def cleanupRunner (ingress : Ingress.Hub Event) (owners : JobOwners)
    (listening : Task (Except IO.Error Unit)) (listener : Std.Internal.UV.TCP.Socket)
    (slots : Slots) (events : Std.CloseableChannel.Sync Event) : IO Unit := do
  ingress.stop
  owners.request
  discard <| IO.wait listening
  closeListener listener
  owners.join
  while let some ev ← events.tryRecv do
    match ev with
    | .accepted c addr | .dialed addr (some c) =>
      SocketAbort.closeIdle c
      slots.release addr
    | .dialed addr none => slots.release addr
    | _ => pure ()

/-- Listen on `port` (0: any) and run a node on this store, keeping
what is from `floor` on (0: everything). -/
def Runner.start {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F)) (db : Db) (floor : Nat)
    (port : UInt16) (notify : List Id → IO Unit := fun _ => pure ()) (cfg : RunConfig := {}) :
    IO Runner := do
  let x := { x with catalog := some (Catalog.sql (F := F)), retryStore := some (RetryStore.sql (F := F)), deferredRetries := true }
  let node := Node.boot x.fam (← (dumpOps (F := F)).run db) floor
  let ch ← eventChannel cfg
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  let writes ← Std.CloseableChannel.Sync.new (some cfg.queue)
  let slots ← Std.Mutex.new []
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, port⟩)
  srv.listen 16
  let bound := match ← srv.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let stopped ← StopFlag.new
  let owners ← JobOwners.new (JobOwners.socketCapacity cfg.maxSocks)
  let listening ← IO.asTask (prio := .dedicated) (acceptor ch srv stopped slots cfg ingress.stopped)
  let turnCounters ← IO.mkRef ({} : TurnCounters)
  let done ← IO.asTask (prio := .dedicated) do
    try runLoop x ch notify cfg writes { db, node, slots, ingress, owners := some owners } turnCounters
    catch e =>
      -- Cancel now; joining belongs to the fixed teardown task below.
      discard <| ingress.stop.toBaseIO
      owners.request
      -- The native shells retain stderr (iOS lean.log / Android logcat).
      -- A background IO failure must not disappear into an unread Task.
      discard <| (IO.eprintln s!"network runner stopped: {e}").toBaseIO
      throw e
  let cleanup ← IO.asTask (prio := .dedicated) do
    discard <| IO.wait done
    cleanupRunner ingress owners listening srv.native slots ch
  let closing ← Std.Mutex.new false
  return {
    events := ch, writes, port := bound, done, stopped, listening, slots, listener := srv.native, closing, turnCounters, ingress
    owners := some owners, cleanup := some cleanup }

/-- Each socket's address and the bytes its lanes hold in the loop's turn.
An unanswered request returns empty after shutdown or runner failure. -/
def Runner.lanes (r : Runner) : IO (List (ByteArray × Nat)) := do
  let p ← IO.Promise.new
  let canceled := do
    return (← r.stopped.get) || (← IO.hasFinished r.done)
  unless ← enqueue r.events (.lanes p) canceled do return []
  repeat
    if ← p.isResolved then return (← IO.wait p.result?).getD []
    if (← canceled) || (← r.events.isClosed) then return []
    IO.sleep 1

/-- Queue local writes for bounded-fair service. Background callers may wait
for space, observing shutdown and runner failure without a channel producer
promise. Unit completion is not an admission receipt: shutdown may cancel the
write. The app uses `writes.trySend` and keeps unaccepted writes. -/
def Runner.write (r : Runner) (ops : List Op) : IO Unit := do
  repeat
    if (← r.stopped.get) || (← r.writes.isClosed) || (← IO.hasFinished r.done) then return
    if ← r.writes.trySend ops then return
    IO.sleep 1

/-- Request loop shutdown and await its fixed owned teardown task. Original
native jobs remain owned beyond the initial loop shutdown grace; callers that
must keep serving UI work await this from their dedicated cleanup task. -/
def Runner.stop (r : Runner) : IO Unit := r.closing.atomically do
  if ← getThe Bool then return
  set true
  r.stopped.request
  r.ingress.stop
  discard <| IO.wait r.done
  if let some cleanup := r.cleanup then
    discard <| IO.wait cleanup
    return
  discard <| IO.wait r.listening
  closeListener r.listener
  while let some ev ← r.events.tryRecv do
    match ev with
    | .accepted c addr | .dialed addr (some c) =>
      -- These clients never reached addSock, so no reader/writer started.
      SocketAbort.closeIdle c
      r.slots.release addr
    | .dialed addr none => r.slots.release addr
    | _ => pure ()

end Engine.Sync
