/- Actual TCP readers, the production Runner/SQLite handlers and its proved
nested selectors. Plain session framing isolates mailbox service; JoinFair
retains production Noise coverage. All payloads and identities are synthetic. -/
import tests.engine.Lib
import tests.engine.SocketAbort
import engine.wire.Tcp
import tests.engine.RunnerWaits
import tests.engine.IngressHub
import engine.core.Exit

namespace IngressTcp
open Engine Engine.Sync Community Tests Std.Async Std.Net

def fam : Family Fact := family ed25519
def author := Device.named "ingress-author"
def rootOp := root author (keyOf author)
def post (n : Nat) := Community.post rootOp.id rootOp.id author "mailbox".toUTF8
  s!"signed ingress message {n}".toUTF8 n (1000 + n)
def session (n : Nat) := sha256 s!"ingress-session-{n}".toUTF8

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 1
  return ← p

structure Peer where
  client : TCP.Socket.Client
  aborter : Option SocketAbort
  address : ByteArray
  cid : Id

def connect (port : UInt16) (n : Nat) : IO Peer := do
  let client ← TCP.Socket.Client.mk
  let .ok _ ← awaitUv (client.native.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, port⟩)) |
    throw (IO.userError "ingress fixture connect failed")
  let aborter ← SocketAbort.capture client
  return ⟨client, aborter, (addrText (← client.getSockName)).toUTF8, session n⟩

def closePeer (peer : Peer) : IO Unit := do
  if let some cap := peer.aborter then discard <| cap.abort
  else SocketAbort.closeIdle peer.client

def setup (established : IO.Ref (List (Id × ByteArray × Bool))) : Sync Fact (SqlM Fact) :=
  { fam, cfg := { every := 1000000000, live := 1000000000 }, hooks := {
    rooms := fun _ => pure [.sync rootOp.id]
    established := do return ← established.get
    sealFor := plainSeal, openFrame := plainOpen } }

def livePeers (hub : Ingress.Hub Event) : IO Nat := hub.registry.atomically do
  let r ← getThe (Ingress.Registry Event hub.peers)
  return (r.live.toArray.toList.filter id).length - 1

def readyPeers (hub : Ingress.Hub Event) : IO Nat := hub.registry.atomically do
  let r ← getThe (Ingress.Registry Event hub.peers)
  return (r.state.slots.toArray.toList.drop 1).countP Option.isSome

def containsFrame (hub : Ingress.Hub Event) (payload : ByteArray) : IO Bool := hub.registry.atomically do
  let r ← getThe (Ingress.Registry Event hub.peers)
  return r.state.slots.toArray.any fun entry => match entry with
    | some (.frame _ bytes) => bytes == payload
    | _ => false

def fairness (t : Checks) : IO Unit := do
  let directory := (← IO.getEnv "INGRESS_RUN_DIR").getD "out/ingress/manual-data"
  IO.FS.createDirAll directory
  let path := directory ++ "/fairness.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  (receive fam [rootOp]).run db
  -- Pinned SQLite uses THREADSAFE=2: each concurrently running reader needs
  -- its own connection, exactly as the app's separate reader does.
  let observer ← Db.openAt path
  let established ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let runner ← IO.mkRef (none : Option Runner)
  let gated ← IO.Promise.new
  let release ← IO.Promise.new
  let active ← IO.mkRef true
  let next ← IO.mkRef 1000
  let own ← IO.mkRef ([(post 500).id] : List Id)
  let commits ← IO.mkRef 0
  let localAt ← IO.mkRef (none : Option (Nat × Nat))
  let markerAt ← IO.mkRef (none : Option Nat)
  let notify := fun ids : List Id => do
    if ids.contains (post 400).id then
      gated.resolve ()
      discard <| IO.wait release.result?
    if let some run ← runner.get then
      if ids.contains (post 500).id then
        let stamp := ((← run.counters).started.toNat, ← IO.monoMsNow)
        localAt.modify (fun _ => some stamp)
      if ids.contains (post 600).id then
        let stamp := (← run.counters).started.toNat
        markerAt.modify (fun _ => some stamp)
      if ids.any (← own.get).contains then
        commits.modify (· + 1)
        if ← active.get then
          let n ← next.modifyGet fun n => (n, n + 1)
          let op := post n
          own.modify (fun _ => [op.id])
          unless ← run.writes.trySend [op] do throw (IO.userError "self-refilling local source lost admission")
          IO.sleep 1
  let cfg : RunConfig := {
    maxSocks := 4, perAddr := 4, queue := 64, tickMs := 20
    stallMs := 3000, stopMs := 500, idle := 1000000000 }
  let run ← Runner.start (setup established) db 0 0 notify cfg
  runner.modify (fun _ => some run)
  let mut peers : List Peer := []
  for i in [:4] do
    let peer ← connect run.port i
    peers := peers ++ [peer]
    discard <| waitFor 1000 do return (← livePeers run.ingress) == i + 1
  let admitted := (← livePeers run.ingress) == 4
  t.ok "four real TCP peers own distinct bounded ingress sources" admitted
  unless admitted do
    active.modify (fun _ => false)
    for peer in peers do closePeer peer
    run.stop
    return
  established.modify (fun _ => peers.map fun peer => (peer.cid, peer.address, false))
  -- The actual write handler follows all configured sessions, then pauses
  -- inside its normal notification after the commit. No selector is mocked.
  run.write [post 400]
  let entered ← waitFor 2000 gated.isResolved
  t.ok "actual committed-write notification gates the production runner" entered
  let some target := peers.getLast? | throw (IO.userError "missing target peer")
  let marker := tagged sealedTag (Codec.encode (target.cid, Codec.encode [(post 600).bytes]))
  let junk : ByteArray := ⟨#[255]⟩
  let sent ← IO.mkRef 0
  let flooding ← peers.take 3 |>.mapM fun peer => IO.asTask (prio := .dedicated) do
    while ← active.get do
      unless ← SocketAbort.awaitSend peer.aborter 2000 (return !(← active.get))
          (peer.client.native.send (Array.replicate 32 (frame junk))) do break
      sent.modify (· + 32)
      IO.sleep 1
  discard <| SocketAbort.awaitSend target.aborter 2000 (pure false)
    (target.client.native.send #[frame marker])
  let controls ← IO.asTask (prio := .dedicated) do
    while ← active.get do
      let reply ← IO.Promise.new
      discard <| run.events.trySend (.lanes reply)
      IO.sleep 1
  let ready ← waitFor 2000 do
    return (← readyPeers run.ingress) == 4 && (← containsFrame run.ingress marker)
  t.ok "honest signed marker is ready in its actual peer mailbox under TCP flood" ready
  let localQueued ← run.writes.trySend [post 500]
  let before ← run.counters
  let started ← IO.monoMsNow
  release.resolve ()
  let delivered ← waitFor 3000 do return (← markerAt.get).isSome && (← localAt.get).isSome
  let committedAt :=  (← localAt.get).getD (before.started.toNat + 1000000, started + 1000000)
  let markerTurn := (← markerAt.get).getD (before.started.toNat + 1000000)
  let localTurns := committedAt.1 - before.started.toNat
  let peerTurns := markerTurn - before.started.toNat
  t.ok "front local write commits within two actual runner turns during peer flood"
    (localQueued && localTurns ≤ 2)
  t.ok "honest peer frame is applied within four times the fixed source count"
    (ready && delivered && peerTurns ≤ 4 * (cfg.maxSocks + 1))
  t.ok "committed local write is immediately readable during the flood"
    ((← (Store.getOp (post 500).id : SqlM Fact _).run observer) == some (post 500))
  t.ok "real local commit remains fast while every sync source is ready" (committedAt.2 - started ≤ 500)
  t.ok "honest marker settles through the actual engine"
    ((← (Store.getStatus (post 600).id : SqlM Fact _).run observer).any fun v => match v with
      | .valid _ => true | _ => false)
  t.ok "peer floods and self-refilling local writes continue through marker delivery"
    ((← sent.get) ≥ 96 && (← commits.get) > 1 && (← active.get))
  IO.println s!"ingress TCP: local={localTurns} turns/{committedAt.2-started}ms, peer={peerTurns}/{4*(cfg.maxSocks+1)} turns, local commits={← commits.get}, flood frames={← sent.get}"
  t.ok "actual runner still has a full peer mailbox when shutdown begins"
    (← waitFor 300 do return (← readyPeers run.ingress) > 0)
  active.modify (fun _ => false)
  for peer in peers do closePeer peer
  run.stop
  for task in flooding do
    let .ok _ ← IO.wait task | throw (IO.userError "TCP flood task failed")
  let .ok _ ← IO.wait controls | throw (IO.userError "control source task failed")
  t.ok "actual runner shuts down with peer producers under backpressure" (← IO.hasFinished run.done)

/-- Descriptor ownership observes the real Runner's otherwise-unretained
reader tasks after shutdown, in addition to the direct task cancellation checks. -/
def fairnessChecked (t : Checks) : IO Unit := do
  if !System.Platform.isWindows then discard <| SocketAbortTest.drained
  IO.sleep 20
  let before ← SocketAbortTest.fdCount
  fairness t
  if System.Platform.isLinux then
    let released ← waitFor 2000 do return (← SocketAbortTest.fdCount) ≤ before
    IO.println s!"ingress descriptors: before={before}, after={← SocketAbortTest.fdCount}"
    t.ok "stopped real runner releases every backpressured peer reader's native handle" released

/-- A completed writer releases native quota before the due-tick reaper.
Actual addSock must still refuse a second retained Sock until close retires
that first source; this runs the production admission and reaping functions. -/
def quotaBeforeReap (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  let established ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let x := setup established
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1, queue := 4, tickMs := 1000000 }
  let ch ← eventChannel cfg
  let slots : Slots ← Std.Mutex.new []
  let (hub, _) ← Ingress.Hub.new (α := Event) cfg.maxSocks
  let initial : RunState := { db, node := Node.boot fam [] 0, slots, ingress := hub }
  let (client, peer) ← SocketAbortTest.pair
  let peerCap ← SocketAbort.capture peer
  let address := "quota-first".toUTF8
  discard <| slots.take cfg address
  let (state, sid) ← RunState.addSock ch cfg initial client address 1
  let some sid := sid | throw (IO.userError "first native source was refused")
  let some sock := state.sockOf (·.id == sid) | throw (IO.userError "missing admitted socket")
  let some source := sock.input | throw (IO.userError "missing admitted source")
  let junk : ByteArray := ⟨#[255]⟩
  discard <| SocketAbort.awaitSend peerCap 1000 (pure false)
    (peer.native.send #[frame junk, frame junk])
  t.ok "actual reader fills its mailbox before writer completion" (← waitFor 1000 (containsFrame hub junk))
  sock.drain
  let finished ← waitFor 1000 (IO.hasFinished sock.done)
  t.ok "actual native writer releases quota while its unreaped source is retained"
    (finished && (← slots.atomically get).isEmpty && (← livePeers hub) == 1 && state.socks.length == 1)
  let (second, secondPeer) ← SocketAbortTest.pair
  let secondCap ← SocketAbort.capture secondPeer
  let address2 := "quota-second".toUTF8
  let reusedQuota ← slots.take cfg address2
  let (still, refused) ← RunState.addSock ch cfg state second address2 2
  t.ok "quota reuse before a due-tick reap cannot grow the retained socket table"
    (reusedQuota && refused.isNone && still.socks.length == 1 && (← livePeers hub) == 1 &&
      (← slots.atomically get).isEmpty)
  unless refused.isNone do
    let writes ← Std.CloseableChannel.Sync.new (some 1)
    discard <| RunState.shutdown x ch cfg writes still 3
    for cap in [peerCap, secondCap] do
      if let some cap := cap then discard <| cap.abort
    return
  let reaped ← RunState.reap x ch (fun _ => pure ()) cfg still 3
  t.ok "actual reap preserves the completed writer's fixed source and admitted frame"
    (reaped.socks.length == 1 && reaped.socks.any (·.closeAfterFrame) &&
      (← livePeers hub) == 1 && !(← source.closed.get) &&
      (← hub.offer source (.frame sid "later frame".toUTF8)) == .closed)
  let premature ← hub.reserve
  t.ok "a frozen source cannot be reused before its retained frame is handled" premature.isNone
  if let some unexpected := premature then hub.retire unexpected
  let selected ← hub.poll (pure none)
  t.ok "the actual selector consumes the originally admitted native frame"
    (selected.any fun ev => match ev with
      | .frame id bytes => id == sid && bytes == junk
      | _ => false)
  let reaped ← match selected with
    | some ev => (fun next => next.getD reaped) <$> reaped.handle x ch (fun _ => pure ()) cfg ev 4
    | none => pure reaped
  t.ok "actual retained-frame handling retires the completed writer's fixed source"
    (reaped.socks.isEmpty && (← livePeers hub) == 0 && (← source.closed.get))
  let (third, thirdPeer) ← SocketAbortTest.pair
  let thirdCap ← SocketAbort.capture thirdPeer
  let address3 := "quota-third".toUTF8
  discard <| slots.take cfg address3
  let (again, accepted) ← RunState.addSock ch cfg reaped third address3 5
  let replacement := accepted.bind fun id => (again.sockOf (·.id == id)).bind (·.input)
  t.ok "retired fixed position is reusable by a subsequent real TCP socket"
    (accepted.isSome && replacement.any (·.index == source.index) && again.socks.length == 1)
  t.ok "an old producer cannot overwrite the actual replacement's mailbox"
    ((← hub.offer source (.frame sid junk)) == .closed)
  let writes ← Std.CloseableChannel.Sync.new (some 1)
  discard <| RunState.shutdown x ch cfg writes again 6
  for cap in [peerCap, secondCap, thirdCap] do
    if let some cap := cap then discard <| cap.abort

/-- Real reader/writer tasks on a real connected socket, retaining the reader
handle solely to observe completion. The same RunState close/shutdown methods
called by Runner must release a reader blocked on its full source mailbox. -/
def readerCancellation (t : Checks) (global : Bool) : IO Unit := do
  let db ← Db.openAt ":memory:"
  let established ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let x := setup established
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1, queue := 1 }
  let (hub, _) ← Ingress.Hub.new (α := Event) 1
  let some source ← hub.reserve | throw (IO.userError "reader cancellation source")
  let ch ← eventChannel cfg
  let slots : Slots ← Std.Mutex.new []
  let (client, peer) ← SocketAbortTest.pair
  let aborter ← SocketAbort.capture client
  let peerCap ← SocketAbort.capture peer
  let stopped ← StopFlag.new
  let out ← Std.Mutex.new ({} : Outbox)
  let wake ← Std.Condvar.new
  let address := "blocked-reader".toUTF8
  discard <| slots.take cfg address
  let reading ← IO.asTask (prio := .dedicated) (reader hub source 0 client stopped)
  let writing ← IO.asTask (prio := .dedicated)
    (writer ch slots 0 client address out wake cfg.burst aborter cfg.stallMs)
  let sock : Sock := {
    id := 0, client, addr := address, heard := 0, stopped
    out, wake, done := writing, aborter, input := some source }
  let state : RunState := { db, node := Node.boot fam [] 0, slots, ingress := hub, socks := [sock] }
  let first : ByteArray := ⟨#[254]⟩
  let next : ByteArray := ⟨#[255]⟩
  discard <| SocketAbort.awaitSend peerCap 1000 (pure false)
    (peer.native.send #[frame first, frame next])
  let ready ← waitFor 1000 (containsFrame hub first)
  IO.sleep 20
  let label := if global then "shutdown" else "retirement"
  t.ok s!"{label} fixture backpressures the actual TCP reader on its own full mailbox"
    (ready && !(← IO.hasFinished reading))
  if global then
    let writes ← Std.CloseableChannel.Sync.new (some 1)
    discard <| RunState.shutdown x ch cfg writes state 10
  else discard <| RunState.close x state 0 10
  let done ← waitFor 500 (IO.hasFinished reading)
  t.ok s!"{label} cancels a real TCP reader blocked on its peer mailbox" done
  t.ok s!"{label} releases the actual socket writer and native quota"
    ((← waitFor 500 (IO.hasFinished writing)) && (← slots.atomically get).isEmpty)
  -- Only after the deadline may a broken closed-send mutation be rescued.
  if !done then
    hub.registry.atomically do
      source.closed.set false
      if h : source.index < hub.peers + 1 then
        modify fun r => { r with
          closed := false
          live := r.live.set source.index true
          accepting := r.accepting.set source.index true
          state := { r.state with slots := Vector.replicate (hub.peers + 1) none } }
    discard <| waitFor 1000 do
      discard <| hub.poll (pure none)
      return ← IO.hasFinished reading
  if let some cap := peerCap then discard <| cap.abort
  if let some cap := aborter then discard <| cap.abort
  let .ok _ ← IO.wait reading | throw (IO.userError "reader cancellation task failed")
  let .ok _ ← IO.wait writing | throw (IO.userError "writer cancellation task failed")

end IngressTcp

def mainBody (args : List String) : IO UInt32 := do
  let t ← Tests.Checks.new
  if args.isEmpty || args.contains "--hub-only" then IngressHub.run t
  if args.isEmpty || args.contains "--fair-only" then IngressTcp.fairnessChecked t
  if args.isEmpty || args.contains "--quota-only" then IngressTcp.quotaBeforeReap t
  if args.isEmpty || args.contains "--cancel-only" then
    IngressTcp.readerCancellation t false
    IngressTcp.readerCancellation t true
  if args.isEmpty || args.contains "--waits-only" then RunnerWaits.run t
  t.finish "ingress-tcp"

/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main (args : List String) : IO UInt32 := Engine.exitAfter (mainBody args)
