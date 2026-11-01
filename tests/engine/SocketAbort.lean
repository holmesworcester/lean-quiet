/- Native SDK ownership/cancellation checks. The actual writer/Slots tests
live in FreshTcp; these keep the original SDK promise observable to reject
early lease release and exercise descriptor lifetime and idle close paths. -/
import engine.wire.SocketAbort
import tests.engine.Checks

namespace SocketAbortTest
open Std Std.Async Std.Net Engine.Sync Tests

def await {α} (operation : IO (IO.Promise (Except IO.Error α))) : IO (Except IO.Error α) := do
  match ← operation.toBaseIO with
  | .error error => return .error error
  | .ok promise =>
    match ← IO.wait promise.result? with
    | some result => return result
    | none => return .error (.userError "promise dropped")

def pair : IO (TCP.Socket.Client × TCP.Socket.Client) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 2
  let address ← server.getSockName
  let client ← TCP.Socket.Client.mk
  let .ok _ ← await (client.native.connect address) |
    throw (IO.userError "native connect failed")
  for _ in [0:2000] do
    if let some accepted ← server.tryAccept then return (client, accepted)
    IO.sleep 1
  throw (IO.userError "native accept timed out")

def waitUntil (milliseconds : Nat) (predicate : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + milliseconds do
    if ← predicate then return true
    IO.sleep 1
  return false

def fdCount : IO Nat := do
  if System.Platform.isLinux then return (← System.FilePath.readDir "/proc/self/fd").size
  return 0

/-- Test the actual SDK promise while the remote peer never reads. -/
def stalled (i : Nat) : IO Bool := do
  let (client, neverReads) ← pair
  let some cap ← SocketAbort.capture client | throw (IO.userError "capture rejected connected idle client")
  let some peerCap ← SocketAbort.capture neverReads | throw (IO.userError "capture peer failed")
  let bytes : ByteArray := ⟨Array.replicate (16 * 1024 * 1024) 97⟩
  let .ok promise ← (client.native.send #[bytes]).toBaseIO |
    throw (IO.userError "native send registration failed")
  IO.sleep 100
  let pending := !(← promise.isResolved)
  let started ← IO.monoMsNow
  let aborted ← cap.abort
  let repeated ← cap.abort
  let resolved ← waitUntil 2000 promise.isResolved
  let failed ← if resolved then do
    match ← IO.wait promise.result? with
    | some (.error _) => pure true
    | _ => pure false
  else pure false
  let ms := (← IO.monoMsNow) - started
  discard <| peerCap.abort
  IO.println s!"stalled {i}: pending={pending}, abort={aborted}, repeat={repeated}, resolved={resolved}, error={failed}, ms={ms}"
  return pending && aborted && repeated && resolved && failed

/-- Written data remains readable after the completed write is shut down. -/
def drained : IO Bool := do
  let (client, receiver) ← pair
  let some cap ← SocketAbort.capture client | throw (IO.userError "capture drain client")
  let some peerCap ← SocketAbort.capture receiver | throw (IO.userError "capture drain peer")
  let payload := "final protocol retirement notice".toUTF8
  let sent ← await (client.native.send #[payload])
  let closed ← cap.abort
  let read ← await (receiver.native.recv? 65536)
  let endOfStream ← await (receiver.native.recv? 65536)
  discard <| peerCap.abort
  let ok := sent.isOk && closed && read.toOption.join == some payload && endOfStream.toOption == some none
  IO.println s!"drained notice before EOF={ok}"
  return ok

def onlyCapability : IO (SocketAbort × TCP.Socket.Client) := do
  let (client, peer) ← pair
  let some cap ← SocketAbort.capture client | throw (IO.userError "capture retained client")
  -- The caller receives no Client reference: the capability alone owns it.
  return (cap, peer)

def lifetime : IO Bool := do
  let (cap, peer) ← onlyCapability
  let some peerCap ← SocketAbort.capture peer | throw (IO.userError "capture retained peer")
  let .ok pending ← (peer.native.recv? 1).toBaseIO | throw (IO.userError "lifetime receive")
  IO.sleep 30
  let heldOpen := !(← pending.isResolved)
  let (other, otherPeer) ← pair
  let some otherCap ← SocketAbort.capture other | throw (IO.userError "capture control")
  let some otherPeerCap ← SocketAbort.capture otherPeer | throw (IO.userError "capture control peer")
  let first ← cap.abort
  let repeated ← cap.abort
  let ended ← waitUntil 1000 pending.isResolved
  let eof ← if ended then do
    match ← IO.wait pending.result? with
    | some (.ok none) => pure true
    | _ => pure false
  else pure false
  let marker := "unrelated socket remains usable".toUTF8
  let sent ← await (other.native.send #[marker])
  let received ← await (otherPeer.native.recv? 65536)
  discard <| otherCap.abort
  discard <| otherPeerCap.abort
  discard <| peerCap.abort
  let ok := heldOpen && first && repeated && eof && sent.isOk && received.toOption.join == some marker
  IO.println s!"capability-only ownership and unrelated descriptor isolation={ok}"
  return ok

def writerDeadline (immediate : Bool) : IO Bool := do
  let (client, peer) ← pair
  let some cap ← SocketAbort.capture client | throw (IO.userError "capture writer")
  let some peerCap ← SocketAbort.capture peer | throw (IO.userError "capture writer peer")
  let stopped ← IO.mkRef false
  let leased ← IO.mkRef true
  let result ← IO.mkRef (none : Option Bool)
  let payload : ByteArray := ⟨Array.replicate (16 * 1024 * 1024) 98⟩
  let began ← IO.monoMsNow
  let .ok original ← (client.native.send #[payload]).toBaseIO |
    throw (IO.userError "writer native send registration")
  let done ← IO.asTask (prio := .dedicated) do
    try
      result.set (some (← SocketAbort.awaitSend (some cap) (if immediate then 5000 else 150)
        stopped.get (pure original)))
    finally leased.set false
  IO.sleep 50
  let reallyPending := !(← IO.hasFinished done) && (← leased.get)
  if immediate then stopped.set true
  let finished ← waitUntil 1500 (IO.hasFinished done)
  let elapsed := (← IO.monoMsNow) - began
  let originalResolved ← original.isResolved
  let ok := reallyPending && finished && originalResolved && !(← leased.get) && (← result.get) == some false &&
    elapsed < 1500 && (immediate || elapsed ≥ 150)
  discard <| peerCap.abort
  IO.println s!"writer {if immediate then "stop" else "deadline after retirement"}: pending={reallyPending}, completed={finished}, lease-released={!(← leased.get)}, elapsed={elapsed}, passed={ok}"
  return ok

def idleClosePaths : IO Bool := do
  let fresh ← TCP.Socket.Client.mk
  let rejected := (← SocketAbort.capture fresh).isNone
  SocketAbort.closeIdle fresh
  SocketAbort.closeIdle fresh
  -- Keep a bound, non-listening socket alive so the refused port cannot be
  -- reused by another process between choosing it and attempting connect.
  let dead ← TCP.Socket.Server.mk
  dead.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  let address ← dead.getSockName
  let failed ← TCP.Socket.Client.mk
  let result ← await (failed.native.connect address)
  SocketAbort.closeIdle failed
  SocketAbort.closeIdle failed
  let ok := rejected && !result.isOk
  IO.println s!"unconnected and failed-connect cleanup without SDK shutdown={ok}"
  return ok

def run (t : Checks) : IO Unit := do
  if System.Platform.isWindows then
    IO.println "SKIP POSIX socket-abort SDK checks; Windows keeps legacy send/close behavior"
    return
  let warm ← drained
  IO.sleep 20
  let before ← fdCount
  let mut repeated := true
  for i in [0:8] do repeated := (← stalled i) && repeated
  t.ok "eight unread 16MiB SDK writes settle their original promises after repeated abort" repeated
  t.ok "completed final-notice bytes precede EOF after POSIX close" ((← drained) && warm)
  t.ok "abort capability alone retains its own descriptor and cannot close an unrelated socket" (← lifetime)
  t.ok "writer-owned deadline waits original SDK promise before cleanup" (← writerDeadline false)
  t.ok "writer stop waits original SDK promise before cleanup" (← writerDeadline true)
  let mut cleaned := true
  for _ in [0:24] do cleaned := (← idleClosePaths) && cleaned
  t.ok "new and refused-connect cleanup is repeatable without SDK shutdown requests" cleaned
  if System.Platform.isLinux then
    let released ← waitUntil 2000 do return (← fdCount) ≤ before
    let after ← fdCount
    IO.println s!"socket-abort descriptors warm-before={before}, after={after}"
    t.ok "repeated abort and failed-connect paths return to exact warmed descriptor baseline" released
  else
    IO.println "SKIP /proc descriptor metric outside Linux; ownership and native IO checks ran"

end SocketAbortTest
