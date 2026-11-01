/-
Raw input policy shared by phones and twin. All samples are retained: a
busy frame cannot discard the move that made a press a drag. The first
pointer owns a gesture; remaining fingers cannot be promoted. Movement
is a high-water mark. InputLaws covers classification and offset bounds.
-/
import engine.renderer.Platform
import engine.renderer.Translate
import engine.renderer.SheetGeom
namespace Input
open App Geometry
structure Point where
  x : Int
  y : Int
  deriving BEq, Repr, Inhabited
structure Touch where
  /-- 0 down, 1 move, 2 up, 3 cancel; monotonic milliseconds. -/
  phase : Nat
  id : Nat
  pos : Point
  time : Nat
  deriving BEq, Repr, Inhabited
structure Context where
  frame : Surface.Frame
  dpi : Nat := 160
  maxB : Nat := 0
  editor : UInt64 := 0
  deriving BEq, Repr, Inhabited

def Context.slop (c : Context) : Nat := 8 * c.dpi / 160

def distance (a b : Point) : Nat := max (a.x - b.x).natAbs (a.y - b.y).natAbs
structure Press where
  first : Touch
  context : Context
  travel : Nat := 0
  held : Bool := false
  deriving BEq, Repr, Inhabited
inductive Gesture where
  | tap (pos : Point)
  | long (pos : Point)
  deriving BEq, Repr

def Press.sample (p : Press) (t : Touch) : Press :=
  { p with travel := max p.travel (distance p.first.pos t.pos) }

def classify (p : Press) (time : Nat) : Option Gesture :=
  if p.travel > p.context.slop ∨ p.held then none
  else if time - p.first.time < 500 then some (.tap p.first.pos)
  else some (.long p.first.pos)

/-- Screen to content in the frame visible when the press began. -/
def content (f : Surface.Frame) (y : Int) : Int :=
  if f.pin then (f.g.composerTop : Int) + f.g.shift - 1 - y
  else (f.b : Int) + f.slide + f.g.composerTop - 1 - y

def region (f : Surface.Frame) (p : Point) : Region :=
  if p.y < f.g.top then .header else if p.y ≥ f.g.composerTop then .composer else .list

def coord (f : Surface.Frame) (p : Point) : Nat :=
  match region f p with
  | .header => p.y.toNat
  | .composer => (p.y - f.g.composerTop).toNat
  | .list => (content f p.y).toNat

def deliver (f : Surface.Frame) : Gesture → Event
  | .tap p => .tap (region f p) p.x.toNat.toUInt32 (coord f p).toUInt32
  | .long p => .long (region f p) p.x.toNat.toUInt32 (coord f p).toUInt32
/-- Diagnostic copy of the list event delivered to the app, never a native
reclassification. Published with the next frame for shell UI tests. -/
def trace (last : Array UInt32) (events : List Event) : Array UInt32 :=
  (events.flatMap fun e => match e with | .action _ _ _ es => es | _ => [e]).foldl (fun last e => match e with
    | .tap .list x y => #[2, x, y]
    | .long .list x y => #[3, x, y]
    | _ => last) last

structure State where
  pointers : List Nat := []
  press : Option Press := none
  offset : Nat := 0
  lastTap : Array UInt32 := #[0, 0, 0]
  serial : Nat := 0
  frames : List (Nat × Context) := []
  deriving BEq, Repr, Inhabited
/-- Revoke gestures and displayed contexts when their mounted page goes away.
Keep the serial monotonic, so a late down cannot name a new page by accident. -/
def revoke (s : State) : State := { s with pointers := [], press := none, frames := [] }

/-- The offset state used by both OS samples and the frame publisher. -/
def sampleOffset (maxB : Nat) (s : State) (sample : Int) : State :=
  { s with offset := Surface.offset maxB sample }

structure Result where
  state : State
  events : List Event := []
  motion : List Touch := []
  deriving BEq, Repr

def drag (p : Press) (t : Touch) : List Event :=
  if region p.context.frame p.first.pos == .composer &&
      (t.phase == 0 || t.phase ≥ 2 || (p.sample t).travel > p.context.slop) then
    let pos := if (p.sample t).travel ≤ p.context.slop then p.first.pos else t.pos
    [.drag t.phase.toUInt32 pos.x.toNat.toUInt32
      (pos.y - p.context.frame.g.composerTop).toNat.toUInt32]
  else []

def follow (s : State) (p : Press) (t : Touch) : Result :=
  if t.id != p.first.id then ⟨s, [], []⟩ else
  let p' := p.sample t
  let ending := t.phase ≥ 2
  let gestures := if t.phase == 2 then (classify p' t.time).toList.map (deliver p.context.frame) else []
  let motion := if region p.context.frame p.first.pos == .list && !p.context.frame.pin then
    if p'.travel > p.context.slop then
      (if p.travel ≤ p.context.slop then [p.first] else []) ++ [t]
    else if ending then [{ t with phase := 3 }] else []
    else []
  ⟨{ s with press := if ending then none else some p' }, drag p t ++ gestures, motion⟩

def touch (c : Context) (s : State) (t : Touch) : Result :=
  if t.phase == 0 then
    if s.pointers.isEmpty then
      let p : Press := ⟨t, c, 0, false⟩
      ⟨{ s with pointers := [t.id], press := some p }, drag p t,
        if region c.frame t.pos == .list && !c.frame.pin then [{ t with phase := 3 }] else []⟩
    else ⟨{ s with pointers := s.pointers ++ [t.id] }, [], []⟩
  else
    let r := match s.press with | none => Result.mk s [] [] | some p => follow s p t
    { r with state := { r.state with pointers :=
        if t.phase ≥ 2 then s.pointers.filter (· != t.id) else s.pointers } }
inductive Raw where
  | owned (ticket owner : UInt64) (refusal : UInt32) (raw : Raw)
  | touch (t : Touch)
  | touchOn (frame : Nat) (t : Touch)
  | touchAt (frame : Nat) (slide : Int) (t : Touch)
  | tick (time : Nat)
  | sample (offset : Int)
  | key (code action : Nat)
  | usbKey (code action : Nat)
  | imeAction (action : Nat)
  | event (e : Event)
  deriving BEq, Repr

def sendKey (enter code action : Nat) : Bool := code == enter && action == 0

def advance (c : Context) (s : State) : Raw → Result
  | .owned ticket admitted refusal raw =>
    let owner := match raw with
      | .touch _ | .touchOn _ _ | .touchAt _ _ _ => (s.press.map (·.context.editor)).getD 0
      | _ => admitted
    let result := advance c s raw
    { result with events := [.action ticket owner (if owner != admitted then 2 else refusal) result.events] }
  | .touch t => touch c s t
  | .touchOn serial t =>
    match s.frames.lookup serial with
    | some shown => touch shown s t
    | none => if t.phase == 0 then ⟨s, [], []⟩ else touch c s t
  | .touchAt serial slide t =>
    match s.frames.lookup serial with
    | some shown => touch { shown with frame := { shown.frame with
        slide := if shown.frame.pin then 0 else slide } } s t
    | none => if t.phase == 0 then ⟨s, [], []⟩ else touch c s t
  | .sample b => ⟨sampleOffset c.maxB s b, [], []⟩
  | .key code action => ⟨s, if sendKey 66 code action then [.send] else [], []⟩
  | .usbKey code action => ⟨s, if sendKey 40 code action then [.send] else [], []⟩
  | .imeAction action => ⟨s, if action == 4 then [.send] else [], []⟩
  | .event e => ⟨s, [e], []⟩
  | .tick time =>
    match s.press with
    | none => ⟨s, [], []⟩
    | some p =>
      if classify p time == some (.long p.first.pos) then
        ⟨{ s with press := some { p with held := true } }, [deliver p.context.frame (.long p.first.pos)], []⟩
      else ⟨s, [], []⟩

/-- Every event, including a range change, revalidates the offset. -/
def step (c : Context) (s : State) (e : Raw) : Result :=
  let r := advance c s e
  { r with state := { r.state with offset := Surface.offset c.maxB r.state.offset } }

def run (c : Context) (s : State) (es : List Raw) : Result :=
  es.foldl (fun r e =>
    let next := step c r.state e
    { next with events := r.events ++ next.events, motion := r.motion ++ next.motion })
    ⟨{ s with offset := Surface.offset c.maxB s.offset }, [], []⟩

/-- A prefix may own only a terminal candidate, never a lifecycle record. -/
def Raw.terminal : Raw → Bool
  | .touchAt _ _ t | .touchOn _ t | .touch t => t.phase == 2
  | .key code action => sendKey 66 code action
  | .usbKey code action => sendKey 40 code action
  | .imeAction action => action == 4
  | _ => false

/-- Eight words: kind, pointer/code, signed x/action, signed y, time low,
time high, displayed frame serial, signed translation. Native queues retain every sample. -/
def decode (ws : Array UInt32) : List Raw := Id.run do
  let mut out := #[]
  let mut pending : Option (UInt64 × UInt64 × UInt32) := none
  for i in [0:ws.size / 8] do
    let k := ws[8*i]!.toNat
    let a := ws[8*i+1]!.toNat
    let b := ws[8*i+2]!
    let d := ws[8*i+3]!
    let time := ws[8*i+4]!.toNat + ws[8*i+5]!.toNat * 4294967296
    if k == 22 then
      if let some (t, o, _) := pending then out := out.push (.event (.action t o 2 []))
      pending := some (ws[8*i+1]!.toUInt64 ||| (b.toUInt64 <<< 32),
        ws[8*i+4]!.toUInt64 ||| (ws[8*i+5]!.toUInt64 <<< 32), d)
      continue
    let raw := if 9 ≤ k && k ≤ 12 then
        some (.touchAt ws[8*i+6]!.toNat ws[8*i+7]!.toInt32.toInt
          ⟨k - 9, a, ⟨b.toInt32.toInt, d.toInt32.toInt⟩, time⟩)
      else if k == 13 then some (.tick time)
      else if k == 14 then some (.key a b.toNat)
      else if k == 15 then some (.usbKey a b.toNat)
      else if k == 5 then some (.imeAction a)
      else if k == 1 then some (.event .close)
      else if k == 4 then some (.event .text)
      else if k == 6 then some (.event (.ime a.toUInt32))
      else if k == 7 then some (.event (.scrolling (a != 0)))
      else if k == 16 then some (.event .background)
      else if k == 17 then some (.event .foreground)
      else if k == 18 then some (.event (.surface (a != 0)))
      else if k == 19 then some (.event .resize)
      else none
    match pending, raw with
    | some (t, o, r), some e =>
      if e.terminal then out := out.push (.owned t o r e)
      else out := (out.push (.event (.action t o 2 []))).push e
    | some (t, o, _), none => out := out.push (.event (.action t o 2 []))
    | none, some e => out := out.push e
    | none, none => pure ()
    pending := none
  if let some (t, o, _) := pending then out := out.push (.event (.action t o 2 []))
  return out.toList

/-- Even an empty terminal classification retains its exact cleanup token. -/
def actionTickets (events : List Event) : List UInt64 :=
  events.filterMap fun e => match e with | .action t _ _ _ => if t == 0 then none else some t | _ => none

def Touch.words (t : Touch) : Array UInt32 :=
  #[(t.phase + 9).toUInt32, t.id.toUInt32, t.pos.x.toInt32.toUInt32, t.pos.y.toInt32.toUInt32,
    t.time.toUInt32, (t.time / 4294967296).toUInt32, 0, 0]
end Input
