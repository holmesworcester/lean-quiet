/- Actual raw decoder, gesture classifier, Session cleanup, and owned-editor
metadata parser. Native/JNI ownership and App submission are checked separately. -/
import engine.renderer.Session
import engine.renderer.Editor

open App Input
namespace OwnedInputCheck

def context : Context :=
  ⟨Surface.make ⟨800, 20, 300, 80, 60⟩ false 32 10 10 704, 160, 100, 7⟩

def envelope (ticket owner : UInt64) (refusal : UInt32 := 0) : Array UInt32 :=
  #[22, ticket.toUInt32, (ticket >>> 32).toUInt32, refusal,
    owner.toUInt32, (owner >>> 32).toUInt32, 0, 0]

def ime : Array UInt32 := #[5, 4, 0, 0, 0, 0, 0, 0]
def background : Array UInt32 := #[16, 0, 0, 0, 0, 0, 0, 0]
def up : Array UInt32 := #[11, 1, 100, 460, 100, 0, 1, 0]

def run (raw : Array UInt32) (state : State := {}) : Result :=
  Input.run context state (Input.decode raw)

def check (count : IO.Ref Nat) (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw <| IO.userError s!"FAIL owned-input: {label}"
  count.modify (· + 1)

def test : IO Unit := do
  let count ← IO.mkRef 0
  let yes := check count
  yes "owned IME keeps exact nonzero token" <|
    (run (envelope 41 7 ++ ime)).events == [.action 41 7 0 [.send]]
  yes "adjacent envelope revokes first token before second Send" <|
    (run (envelope 41 7 ++ envelope 42 7 ++ ime)).events ==
      [.action 41 7 2 [], .action 42 7 0 [.send]]
  yes "orphan envelope remains an explicit cleanup envelope" <|
    (run (envelope 41 7)).events == [.action 41 7 2 []]
  yes "lifecycle record cannot be swallowed by malformed ownership" <|
    (run (envelope 41 7 ++ background)).events == [.action 41 7 2 [], .background]
  yes "unknown record retires preceding token" <|
    (run (envelope 41 7 ++ #[99,0,0,0,0,0,0,0])).events == [.action 41 7 2 []]
  yes "truncated record cannot conceal retained token" <|
    (run (envelope 41 7 ++ #[5,4,0])).events == [.action 41 7 2 []]
  yes "ignored Up still has one exact cleanup token" <|
    (run (envelope 41 7 ++ up)).events == [.action 41 0 2 []]
  let down := Input.run context {frames := [(1,context)]}
    [.touchOn 1 ⟨0,1,⟨100,460⟩,0⟩]
  yes "test premise has live compositor drag" <|
    down.state.press.isSome && down.events == [.drag 0 100 20]
  let released := run (envelope 41 7 ++ up) down.state
  yes "one Up envelope owns both drag termination and tap" <|
    released.events == [.action 41 7 0 [.drag 2 100 20,.tap .composer 100 20]]
  yes "terminal classification retires press" released.state.press.isNone
  let stale := run (envelope 41 8 ++ up) down.state
  yes "replacement editor cannot acquire held gesture" <|
    stale.events == [.action 41 7 2 [.drag 2 100 20,.tap .composer 100 20]]
  yes "refusal keeps terminal native motion and pointer cleanup" <|
    stale.motion == released.motion && stale.state.press.isNone
  let busy := run (envelope 0 7 1 ++ up) down.state
  yes "busy Up retains cancellation information without fake token" <|
    busy.events == [.action 0 7 1 [.drag 2 100 20,.tap .composer 100 20]] &&
    (Input.actionTickets busy.events).isEmpty
  let tickets := Input.actionTickets (run (envelope 41 7 ++ envelope 42 7 ++ up)).events
  yes "empty classifications participate in batch cleanup" (tickets == [41,42])
  yes "full UInt64 token survives wire split" <|
    Input.actionTickets (run (envelope 4294967337 8589934599 ++ ime)).events == [4294967337]
  let retired ← IO.mkRef ([] : List UInt64)
  let motionRan ← IO.mkRef false
  let failed ← try
      discard <| Session.receive (fun _ => do
        motionRan.set true
        throw <| IO.userError "injected motion failure")
        context down.state (envelope 41 7 ++ envelope 42 7 ++ up)
        (fun t => retired.modify (· ++ [t]))
      pure false
    catch e => pure (e.toString == "injected motion failure")
  yes "actual throwing motion retains its error" (failed && (← motionRan.get))
  yes "Session retires each token before propagating motion exception" <|
    (← retired.get) == [41,42]
  retired.set []
  let received ← Session.receive (fun _ => pure ()) context down.state
    (envelope 41 7 ++ up) (fun t => retired.modify (· ++ [t]))
  yes "successful Session hands ownership to App without early retirement" <|
    received.events == released.events && (← retired.get).isEmpty
  yes "allocation error is never a valid empty snapshot" <|
    (Editor.snapshot ("",#[2])).isNone
  yes "allocation error is never a valid new empty draft" <|
    (Editor.latest ("",#[2])).isNone
  let snapshot := Editor.snapshot ("A",#[41,7,11,13,1,1,0,0])
  yes "snapshot parser retains text and independent content version" <|
    snapshot == some ⟨41,7,11,13,"A",#[1,1,0,0]⟩
  let latest := Editor.latest ("B",#[1,7,12,1,41,0,1,1,0,0,0,7])
  yes "newer native draft is distinct from clearing consumed action" <|
    latest == some ⟨7,12,true,41,false,false,7,"B",#[1,1,0,0]⟩
  IO.println s!"owned-input: {← count.get} passed, 0 failed"

end OwnedInputCheck

def main : IO Unit := OwnedInputCheck.test
