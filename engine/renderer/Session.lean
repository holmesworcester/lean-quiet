/- The shared frame boundary: publish Lean's rectangles, consume raw events,
and return only Lean-classified events and accepted physics samples. -/
import engine.renderer.Input
import engine.renderer.Hold
namespace Session
abbrev Show := Array ByteArray → UInt32 → UInt32 → Array ByteArray → Array ByteArray →
  Bool → Array UInt32 → Array ByteArray → IO (Array UInt32)

/-- Consume raw events with the last published frame, also without a surface. -/
def receive (motion : Array UInt32 → IO Unit) (context : Input.Context)
    (state : Input.State) (raw : Array UInt32) (retire : UInt64 → IO Unit := fun _ => pure ()) : IO Input.Result := do
  let result := Input.run context state (Input.decode raw)
  try motion (result.motion.foldl (fun ws t => ws ++ t.words) #[])
  catch e =>
    for ticket in Input.actionTickets result.events do retire ticket
    throw e
  return { result with state := { result.state with lastTap := Input.trace state.lastTap result.events } }

/-- Android reports whether it accepted this publication. Synchronous shells
without a status record accept on return. Records share the raw eight-word ABI. -/
def accepted (raw : Array UInt32) : Bool := Id.run do
  for i in [0:raw.size / 8] do
    if raw[i * 8]! == 20 && raw[i * 8 + 1]! == 0 then return false
  return true

/-- Native asynchronous shells report a monotone publication ticket separately
from the wrapped UInt32 input-frame serial. Synchronous shells omit kind 20's
ticket and kind 21; returning from their frame function completes this frame. -/
def publication (raw : Array UInt32) (serial : UInt64) : UInt64 := Id.run do
  for i in [0:raw.size / 8] do
    if raw[i * 8]! == 20 then
      return raw[i * 8 + 2]!.toUInt64 ||| (raw[i * 8 + 3]!.toUInt64 <<< 32)
  return serial

/-- Kind 21 carries the completed publication ticket in words 4/5 and actual
native translation in word 3. Explicit absence never falls back to acceptance. -/
def completed (raw : Array UInt32) (serial : UInt64) : Option (UInt64 × UInt32) := Id.run do
  for i in [0:raw.size / 8] do
    if raw[i * 8]! == 21 then
      return if raw[i * 8 + 2]! == 1 then
        some (raw[i * 8 + 4]!.toUInt64 ||| (raw[i * 8 + 5]!.toUInt64 <<< 32), raw[i * 8 + 3]!)
      else none
  return if accepted raw then some (serial, 0) else none

structure Presented extends Input.Result where
  accepted : Bool
  publication : UInt64
  completed : Option (UInt64 × UInt32)

def present (display : Show) (motion : Array UInt32 → IO Unit) (g : Geometry.Geom)
    (dpi maxB : Nat) (state : Input.State) (list : Array ByteArray) (b over : Nat)
    (top bot : Array ByteArray) (pin : Bool) (hold : Array ByteArray := #[]) (holdPeriod : Nat := 48) (editor : UInt64 := 0)
    (retire : UInt64 → IO Unit := fun _ => pure ()) : IO Presented := do
  let state := Input.sampleOffset maxB state b
  let frame := Surface.make g pin over b state.offset list.size
  let context : Input.Context := ⟨frame, dpi, maxB, editor⟩
  let serial := state.serial + 1
  -- A failed publication cannot evict the frame still visible on the device.
  let state := { state with serial := serial }
  let width := ((list[0]?).getD ByteArray.empty).size / 4
  let hold := if hold.isEmpty then
      Hold.plane ⟨Paint.solid Row.bg width, ⟨dpi, 0, .dark, none⟩, width⟩ g.viewNow else hold
  let high := b + g.view + over
  let words := frame.words.push serial.toUInt32 ++ state.lastTap ++
    #[frame.origin.toInt32.toUInt32, list.size.toUInt32, (if pin then 1 else 0),
      ((high : Int) - list.size).toInt32.toUInt32, high.toUInt32,
      hold.size.toUInt32, holdPeriod.toUInt32, Row.placeholder, Row.bg]
  let raw ← display list b.toUInt32 over.toUInt32 top (Surface.fill g bot) pin words hold
  let published := accepted raw
  -- Drain touches against all previously accepted contexts before pruning:
  -- the oldest frame may still have been visible when this batch was acquired.
  let pending := if published then (serial, context) :: state.frames else state.frames
  let result ← receive motion context { state with frames := pending } raw retire
  let retained := if published then (serial, context) :: state.frames.take 2 else state.frames
  return ⟨{ result with state := { result.state with frames := retained } },
    published, publication raw serial.toUInt64, completed raw serial.toUInt64⟩
end Session
