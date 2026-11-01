/- Native desktop publication metadata. Buffering App layers is not a native
publication. Native shells return four-word records alongside desktop events;
completion names a nonzero UInt64 publication ticket and submitted translation. -/
import engine.renderer.Session

namespace Desktop.Publication

structure Result where
  events : Array UInt32 := #[]
  accepted : Bool := false
  /-- The one publication selected for native completion tracking. -/
  tracking : Option UInt64 := none
  completed : Option (UInt64 × UInt32) := none

/-- The App-facing adapter always reports staging without completion. -/
def staged (ticket : UInt64) : Array UInt32 :=
  #[20, 1, ticket.toUInt32, (ticket >>> 32).toUInt32, 0, 0, 0, 0,
    21, 0, 0, 0, 0, 0, 0, 0]

def rejected : Array UInt32 := #[20, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0]

/-- Fail closed when a native shell omits its explicit publication status. -/
def decode (raw : Array UInt32) : Result := Id.run do
  let mut result : Result := { events := raw }
  for i in [0:raw.size / 4] do
    if raw[i * 4]! == 20 then
      let id := raw[i * 4 + 2]!.toUInt64 ||| (raw[i * 4 + 3]!.toUInt64 <<< 32)
      result := { result with accepted := raw[i * 4 + 1]! == 1, tracking := if id == 0 then none else some id }
    if raw[i * 4]! == 21 then
      let id := raw[i * 4 + 1]!.toUInt64 ||| (raw[i * 4 + 2]!.toUInt64 <<< 32)
      result := { result with completed := if id == 0 then none else some (id, raw[i * 4 + 3]!) }
  return result

/-- A refused native publication has not installed the current hit geometry.
Cancel positional gestures instead of dispatching stale coordinates; keep
text/key/close events. Accepted redraws need not await a completion callback. -/
def forInput (r : Result) : Array UInt32 := Id.run do
  if r.accepted then return r.events
  let mut out := #[]
  for i in [0:r.events.size / 4] do
    if !([2, 3, 9, 10, 11, 14, 19] : List UInt32).contains r.events[i*4]! then
      out := out ++ r.events.extract (i*4) (i*4+4)
  return out ++ #[16, 0, 0, 1]

end Desktop.Publication
