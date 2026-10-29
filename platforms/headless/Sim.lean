/-
The app without a window, for tests: an `Io` made of refs (the offset, the
control commands and replies, the last frames), the screen as the twin
composes it, PPM screenshots, and waiting for the writer.
-/
import Quiet
import engine.renderer.TranslatePaint

open App Engine Community Data

structure Sim where
  b : IO.Ref Float
  replies : IO.Ref (Array String)
  cmds : IO.Ref (Array String)
  last : IO.Ref (Array ByteArray × Nat × Nat × Array ByteArray × Array ByteArray)
  placement : IO.Ref (Array UInt32)
  hold : IO.Ref (Array ByteArray)
  raw : IO.Ref (Array UInt32)
  maxB : IO.Ref Float
  /-- What the camera shows (a luma frame), and where its preview is. -/
  camera : IO.Ref (Array UInt32 × ByteArray)
  on : IO.Ref Bool
  /-- The native text field's text (setText writes it, text reads it). -/
  native : IO.Ref String
  viewport : IO.Ref (Array UInt32)
  keyboard : IO.Ref Bool
  events : IO.Ref (Array UInt32)
  urls : IO.Ref (Array String)
  visible : IO.Ref Bool
  frames : IO.Ref Nat

/-- Two loopback ports for a test's two nodes, from its process id: tests
running at once (in other worktrees too) get different ports, below
Linux's ephemeral range so no outbound socket holds them. -/
def testPorts : IO (Nat × Nat) := do
  let p := 20000 + (← IO.Process.getPID).toNat % 5000 * 2
  return (p, p + 1)

def Sim.new : IO Sim := do
  return ⟨← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef (#[], 0, 0, #[], #[]), ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0,
    ← IO.mkRef (#[], .empty), ← IO.mkRef false,
    ← IO.mkRef "", ← IO.mkRef #[1080, 2400, 128, 63, 420], ← IO.mkRef false,
    ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef true, ← IO.mkRef 0⟩

def Sim.input (sm : Sim) : IO.Ref String := sm.native

def Sim.io (sm : Sim) : Io where
  screen := sm.viewport.get
  scroll ch vh := do
    let mx := if ch > vh then (ch - vh).toNat.toFloat else 0
    sm.maxB.set mx
    sm.b.get
  scrollBy d := sm.b.modify (· + d)
  scrollTo b := sm.b.set b
  frame fr b o top bot _ placement hold := do
    unless ← sm.visible.get do throw (IO.userError "frame without a surface")
    sm.frames.modify (· + 1)
    sm.hold.set hold
    sm.last.set (fr, b.toNat, o.toNat, top, bot)
    sm.placement.set placement
    sm.raw.modifyGet fun es => (es, #[])
  text := do return (← sm.native.get, #[0, 0, 0, 0])
  ime on := sm.keyboard.set on
  setText := sm.native.set
  copy t := sm.replies.modify (·.push s!"copied {t}")
  ctlPoll := sm.cmds.modifyGet fun c => (c, #[])
  ctlReply s := sm.replies.modify (·.push s)
  nowUs := do return (← IO.monoNanosNow).toUInt64 / 1000
  scan on := sm.on.set on
  poll := sm.events.modifyGet fun es => (es, #[])
  links := sm.urls.modifyGet fun us => (us, #[])
  luma := do
    if !(← sm.on.get) then return (#[], .empty)
    sm.camera.get

/-- The screen as the twin composes it: header, the list's viewport rows,
the composer above the bottom inset. -/
def screenOf (sm : Sim) (W Hs insetBot : Nat) : IO (Array ByteArray) := do
  let (fr, _, _, top, bot) ← sm.last.get
  let _ := insetBot
  return Translate.compose (← sm.placement.get) (← sm.b.get).toInt64.toInt32 Hs
    (bot.back?.getD (Paint.solid (Palette.color .light .bg) W)) fr top bot (← sm.hold.get)

def writePpm (path : String) (W : Nat) (rows : Array ByteArray) : IO Unit := do
  let mut b := s!"P6\n{W} {rows.size}\n255\n".toUTF8
  for r in rows do
    for i in [0:W] do
      b := b.push r[4*i]! |>.push r[4*i+1]! |>.push r[4*i+2]!
  IO.FS.writeBinFile path b

def steps (n : Nat) : M Unit := do
  for _ in [0:n] do
    let _ ← step []

def waitIdle (sm : Sim) : M Unit := do
  -- wait for a new idle reply: earlier ones are still in the replies
  let before := ((← sm.replies.get).filter (·.startsWith "idle")).size
  sm.cmds.modify (·.push "wait")
  let mut k := 0
  while ((← sm.replies.get).filter (·.startsWith "idle")).size == before && k < 20000 do
    let _ ← step []
    IO.sleep 1
    k := k + 1
  -- let paints finish
  for _ in [0:30] do
    let _ ← step []
    IO.sleep 2

