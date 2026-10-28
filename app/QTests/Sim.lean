/-
The app without a window, for tests: an `Io` made of refs (the offset, the
control commands and replies, the last frames), the screen as the twin
composes it, PPM screenshots, and waiting for the writer.
-/
import Quiet

open App Engine Community Data

structure Sim where
  b : IO.Ref Float
  replies : IO.Ref (Array String)
  cmds : IO.Ref (Array String)
  last : IO.Ref (Array ByteArray × Nat × Nat × Array ByteArray × Array ByteArray)
  maxB : IO.Ref Float
  /-- What the camera shows (a luma frame), and where its preview is. -/
  camera : IO.Ref (Array UInt32 × ByteArray)
  on : IO.Ref Bool

def Sim.new : IO Sim := do
  return ⟨← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef (#[], 0, 0, #[], #[]), ← IO.mkRef 0,
    ← IO.mkRef (#[], .empty), ← IO.mkRef false⟩

def Sim.io (sm : Sim) : Io where
  screen := pure #[1080, 2400, 128, 63, 420]
  scroll ch vh := do
    let mx := if ch > vh then (ch - vh).toNat.toFloat else 0
    sm.maxB.set mx
    let b ← sm.b.get
    let b := if b < 0 then 0 else if b > mx then mx else b
    sm.b.set b
    return b.toUInt32
  scrollBy d := sm.b.modify (· + d)
  scrollTo b := sm.b.set b
  frame fr b o top bot _ := do sm.last.set (fr, b.toNat, o.toNat, top, bot); return #[]
  text := pure ("", #[0, 0, 0, 0])
  ime _ := pure ()
  textClear := pure ()
  copy t := sm.replies.modify (·.push s!"copied {t}")
  ctlPoll := sm.cmds.modifyGet fun c => (c, #[])
  ctlReply s := sm.replies.modify (·.push s)
  nowUs := do return (← IO.monoNanosNow).toUInt64 / 1000
  scan on := sm.on.set on
  luma := do
    if !(← sm.on.get) then return (#[], .empty)
    sm.camera.get

/-- The screen as the twin composes it: header, the list's viewport rows,
the composer above the bottom inset. -/
def screenOf (sm : Sim) (W Hs insetBot : Nat) : IO (Array ByteArray) := do
  let (fr, _, o, top, bot) ← sm.last.get
  let bg := bot.back?.getD (Paint.solid (Palette.color .light .bg) W)
  let mut out := Array.replicate Hs bg
  for i in [0:top.size] do out := out.set! i top[i]!
  let vh := Hs - top.size - bot.size - insetBot
  for r in [0:vh] do
    if let some row := fr[o + r]? then out := out.set! (top.size + r) row
  for i in [0:bot.size] do out := out.set! (top.size + vh + i) bot[i]!
  return out

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

