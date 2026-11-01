/- Native component regression for the actual reader/writer ownership core.
An explicit continuation gate delays the original reader task's completion;
this is a controlled task-lifetime test, not a literal OS thread suspension.
Separate actual addSock coverage checks the production callback wiring. -/
import tests.engine.SocketAbort
import tests.engine.HardenLib

open Engine Engine.Sync Tests Std.Async Std.Net

namespace ReaderLease

def waitFor (ms : Nat) (ready : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← ready then return true
    IO.sleep 1
  return false

def sourceLive (hub : Ingress.Hub Event) (source : Ingress.Source) : IO Bool :=
  hub.registry.atomically do
    let r ← getThe (Ingress.Registry Event hub.peers)
    return r.live.toArray[source.index]?.getD false

/-- While one dedicated writer waits for its reader, a second real runner
continues accepting TCP and committing local work. -/
def independentWork (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  let op := Op.make 240 [] "reader cleanup must not block this commit".toUTF8
  let committed ← IO.Promise.new
  let x : Sync Nat (SqlM Nat) := {
    fam := Harden.fam
    hooks := { rooms := fun _ => pure [], sealFor := plainSeal, openFrame := plainOpen } }
  let run ← Runner.start x db 0 0 (fun ids => if ids.contains op.id then committed.resolve () else pure ())
  let peer ← TCP.Socket.Client.mk
  let .ok _ ← awaitUv (peer.native.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, run.port⟩)) |
    throw (IO.userError "independent peer connect")
  let admitted ← waitFor 1000 do return !(← run.slots.atomically get).isEmpty
  run.write [op]
  let wrote ← waitFor 1000 committed.isResolved
  t.ok "independent actual TCP admission continues while reader cleanup waits" admitted
  t.ok "independent actual local commit continues while reader cleanup waits" wrote
  run.stop
  SocketAbort.closeIdle peer

/-- The same cleanup function passed by addSock to writer must retain the
public native quota until the original reader task has actually completed. -/
def gated (t : Checks) : IO Unit := do
  let (client, peer) ← SocketAbortTest.pair
  let aborter ← SocketAbort.capture client
  let peerAborter ← SocketAbort.capture peer
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1 }
  let slots : Slots ← Std.Mutex.new []
  let addr := "gated-reader".toUTF8
  let reserved ← slots.take cfg addr
  let (hub, _) ← Ingress.Hub.new (α := Event) cfg.maxSocks
  let some source ← hub.reserve | throw (IO.userError "gated reader source")
  let held := "retained mailbox head".toUTF8
  let offered ← hub.offer source (.frame 0 held)
  let stopped ← StopFlag.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let reading ← IO.asTask (prio := .dedicated) do
    reader hub source 0 client stopped
    entered.resolve ()
    discard <| IO.wait release.result?
  -- A real framed TCP payload reaches an already full source. Either the
  -- reader is backpressured there or recv cancellation races registration.
  let sent ← SocketAbort.awaitSend peerAborter 1000 (pure false)
    (peer.native.send #[frame "next real frame".toUTF8])
  IO.sleep 30
  let ch ← eventChannel { queue := 1 }
  let out ← Std.Mutex.new ({ stopped := true } : Outbox)
  let wake ← Std.Condvar.new
  let writing ← IO.asTask (prio := .dedicated)
    (writer ch slots 0 client addr out wake cfg.burst aborter 150
      (finishReader stopped client reading))
  let readerExited ← waitFor 1000 entered.isResolved
  t.ok "writer cleanup stops the actual backpressured reader body"
    (reserved && offered == .accepted && sent && readerExited)
  t.ok "native quota remains held while the original reader task exit is gated"
    (!(← IO.hasFinished reading) && !(← IO.hasFinished writing) &&
      !(← slots.atomically get).isEmpty)
  t.ok "writer cleanup keeps source ownership until main close or reap"
    ((← sourceLive hub source) && !(← source.closed.get))
  independentWork t
  -- Failure cleanup starts only after the lifetime and progress assertions.
  stopped.request
  discard <| client.native.cancelRecv.toBaseIO
  release.resolve ()
  let finished ← waitFor 1000 (IO.hasFinished writing)
  t.ok "writer releases quota only after original reader task completion"
    (finished && (← IO.hasFinished reading) && (← slots.atomically get).isEmpty)
  let next := "next-peer".toUTF8
  let admitted ← slots.take cfg next
  t.ok "reader completion permits a subsequent native reservation" admitted
  if admitted then slots.release next
  hub.retire source
  if let some cap := peerAborter then discard <| cap.abort

/-- This uses production addSock without an injected reader or writer.
Stopping its writer must invoke the wired cleanup, even before main reaps. -/
def wiring (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  let x : Sync Nat (SqlM Nat) := {
    fam := Harden.fam
    hooks := { rooms := fun _ => pure [], sealFor := plainSeal, openFrame := plainOpen } }
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1 }
  let ch ← eventChannel cfg
  let slots : Slots ← Std.Mutex.new []
  let (hub, _) ← Ingress.Hub.new (α := Event) cfg.maxSocks
  let (client, peer) ← SocketAbortTest.pair
  let peerAborter ← SocketAbort.capture peer
  let addr := "actual-addSock-reader".toUTF8
  let reserved ← slots.take cfg addr
  let state : RunState := { db, node := Node.boot Harden.fam [] 0, slots, ingress := hub }
  let (state, sid) ← state.addSock ch cfg client addr 0
  let some sock := sid.bind fun id => state.sockOf (·.id == id) |
    throw (IO.userError "production addSock rejected reader fixture")
  let some source := sock.input | throw (IO.userError "production addSock omitted source")
  let offered ← hub.offer source (.frame sock.id "held until reap".toUTF8)
  sock.out.atomically (modify fun out => { out with stopped := true })
  sock.wake.notifyAll
  let ended ← waitFor 1000 (IO.hasFinished sock.done)
  t.ok "production addSock writer stops and joins its original reader task"
    (reserved && offered == .accepted && ended && (← sock.stopped.get) &&
      (← IO.hasFinished sock.readerDone) && (← slots.atomically get).isEmpty)
  t.ok "completed socket keeps fixed source until actual RunState.reap"
    ((← sourceLive hub source) && !(← source.closed.get) && state.socks.length == 1)
  -- Also terminates a missing-callback negative control before fixture exit.
  sock.stopped.request
  discard <| client.native.cancelRecv.toBaseIO
  discard <| waitFor 1000 (IO.hasFinished sock.readerDone)
  let reaped ← state.reap x ch (fun _ => pure ()) cfg 1
  t.ok "actual reap removes completed socket and retires its source"
    (reaped.socks.isEmpty && (← source.closed.get) && !(← sourceLive hub source))
  if let some cap := peerAborter then discard <| cap.abort

def run (t : Checks) : IO Unit := do
  if System.Platform.isWindows then
    IO.println "SKIP reader lease native control (POSIX abort prerequisite)"
    return
  gated t
  wiring t

end ReaderLease
