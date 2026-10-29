/- The shared frame boundary: publish Lean's rectangles, consume raw events,
and return only Lean-classified events and accepted physics samples. -/
import engine.renderer.Input
import engine.renderer.Hold
namespace Session
abbrev Show := Array ByteArray → UInt32 → UInt32 → Array ByteArray → Array ByteArray →
  Bool → Array UInt32 → Array ByteArray → IO (Array UInt32)

/-- Consume raw events with the last published frame, also without a surface. -/
def receive (motion : Array UInt32 → IO Unit) (context : Input.Context)
    (state : Input.State) (raw : Array UInt32) : IO Input.Result := do
  let result := Input.run context state (Input.decode raw)
  motion (result.motion.foldl (fun ws t => ws ++ t.words) #[])
  return { result with state := { result.state with lastTap := Input.trace state.lastTap result.events } }

/-- Android reports whether it accepted this publication. Synchronous shells
without a status record accept on return. Records share the raw eight-word ABI. -/
def accepted (raw : Array UInt32) : Bool := Id.run do
  for i in [0:raw.size / 8] do
    if raw[i * 8]! == 20 && raw[i * 8 + 1]! == 0 then return false
  return true

def present (display : Show) (motion : Array UInt32 → IO Unit) (g : Geometry.Geom)
    (dpi maxB : Nat) (state : Input.State) (list : Array ByteArray) (b over : Nat)
    (top bot : Array ByteArray) (pin : Bool) (hold : Array ByteArray := #[]) : IO Input.Result := do
  let state := Input.sampleOffset maxB state b
  let frame := Surface.make g pin over b state.offset list.size
  let context : Input.Context := ⟨frame, dpi, maxB⟩
  let serial := state.serial + 1
  -- A failed publication cannot evict the frame still visible on the device.
  let state := { state with serial := serial }
  let width := ((list[0]?).getD ByteArray.empty).size / 4
  let hold := if hold.isEmpty then
      Hold.plane ⟨Paint.solid Row.bg width, ⟨dpi, 0, .dark⟩, width⟩ g.viewNow else hold
  let high := b + g.view + over
  let words := frame.words.push serial.toUInt32 ++ state.lastTap ++
    #[frame.origin.toInt32.toUInt32, list.size.toUInt32, (if pin then 1 else 0),
      ((high : Int) - list.size).toInt32.toUInt32, high.toUInt32,
      hold.size.toUInt32, 48, Row.placeholder, Row.bg]
  let raw ← display list b.toUInt32 over.toUInt32 top (Surface.fill g bot) pin words hold
  let published := accepted raw
  -- Drain touches against all previously accepted contexts before pruning:
  -- the oldest frame may still have been visible when this batch was acquired.
  let pending := if published then (serial, context) :: state.frames else state.frames
  let result ← receive motion context { state with frames := pending } raw
  let retained := if published then (serial, context) :: state.frames.take 2 else state.frames
  return { result with state := { result.state with frames := retained } }
end Session
