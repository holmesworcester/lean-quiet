import Std.Async.TCP

namespace Engine.Sync

private opaque SocketAbortImpl : NonemptyType
def SocketAbort := SocketAbortImpl.type

/-- Capture before starting any client read/write task. The capability owns
one Lean reference to the exact native socket whose descriptor was captured. -/
@[extern "lq_socket_abort_capture"]
private opaque captureNative (socket : @& Std.Internal.UV.TCP.Socket) : IO (Option SocketAbort)

def SocketAbort.capture (client : Std.Async.TCP.Socket.Client) : IO (Option SocketAbort) := do
  -- This SDK call takes the UV mutex, so even the tail of a just-resolved
  -- connect callback finishes before descriptor capture. No reader/writer
  -- may be started until capture returns. Its address result is irrelevant.
  discard <| client.native.getSockName.toBaseIO
  captureNative client.native

/-- Shuts down both directions, retaining libuv's descriptor ownership.
The capability keeps the descriptor's native socket alive throughout the call. -/
@[extern "lq_socket_abort"]
opaque SocketAbort.abort (capability : @& SocketAbort) : IO Bool

/-- Wait for the SDK callback's tail after its promise was published. This
uses the SDK's UV mutex from the dedicated writer task, not from a UV callback. -/
@[extern "lq_socket_abort_barrier"]
opaque SocketAbort.barrier (capability : @& SocketAbort) : IO Unit

/-- Close a new, failed-connect or otherwise idle client without entering
the SDK's uv_shutdown request path. Outstanding sends must use the capability
captured *before* they started instead. A never-opened descriptor needs no
shutdown; normal Lean ownership eventually finalizes its idle UV handle. -/
def SocketAbort.closeIdle (client : Std.Async.TCP.Socket.Client) : IO Unit := do
  discard <| client.native.cancelRecv.toBaseIO
  if let some cap ← SocketAbort.capture client then discard <| cap.abort

/-- Wait for the *existing* SDK send promise; no substitute promise is
completed and no slot may be released before that promise settles. A writer
owns this deadline even after protocol retirement removes it from RunState.
Unsupported platforms retain the old wait, without claiming cancellation. -/
def SocketAbort.awaitSend (aborter : Option SocketAbort) (stallMs : Nat)
    (stopped : IO Bool) (operation : IO (IO.Promise (Except IO.Error Unit))) : IO Bool := do
  let .ok promise ← operation.toBaseIO | return false
  match aborter with
  | none =>
    return (← IO.wait promise.result?).any fun result => result.isOk
  | some cap =>
    let since ← IO.monoMsNow
    let mut attempted := false
    repeat
      if ← promise.isResolved then
        let result ← IO.wait promise.result?
        cap.barrier
        return result.any fun result => result.isOk
      if !attempted && ((← IO.monoMsNow) ≥ since + stallMs || (← stopped)) then
        attempted := true
        unless ← cap.abort do
          IO.eprintln "socket abort failed; retaining lease until native write completes"
      IO.sleep 1

end Engine.Sync
