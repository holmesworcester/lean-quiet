/-
Issue #3 on the headless app: send Hebrew/Arabic messages through the
writer, wait for their painted rows, and compare the clock's pixels with
five independently painted glyphs in logical order. Also checks names
through oneLine. Screens and row bitmaps are retained. No laws here.
-/
import platforms.headless.Sim

namespace BidiHost
open App Engine Community Data

def clockChars : List UInt32 := [0x31, 0x32, 0x3A, 0x33, 0x30]

/-- A reference strip painted directly from the five expected glyphs;
no bidi, layout, or placement code participates in this oracle. -/
def reference (f : Font.Font) : Paint.Bitmap := Id.run do
  let w := (clockChars.map (Text.adv f)).sum
  let mut bmp := Paint.Bitmap.blank w f.cell (Paint.solid Row.bg w)
  let mut x := 0
  for c in clockChars do
    bmp := bmp.glyph f c x 0 Row.ink false
    x := x + Text.adv f c
  return bmp

def stripEq (actual expected : Paint.Bitmap) (x y : Nat) : Bool := Id.run do
  if x + expected.w > actual.w || y + expected.h > actual.h then return false
  for j in [:expected.h] do
    for i in [:expected.w] do
      if Paint.getPx actual.rows[y+j]! (x+i) != Paint.getPx expected.rows[j]! i then return false
  return true

def clockOrder (line : Text.Line) : Bool :=
  let digits := line.toList.filter (fun g => clockChars.contains g.c)
  digits.map (·.c) == clockChars &&
    (digits.zip digits.tail).all (fun (a, b) => a.x < b.x)

def settle : M Unit := do
  for _ in [:1000] do
    steps 1
    let s ← get
    if let some (_, x) := s.ids[0]? then
      if let some r := s.rows[x]? then
        if !r.data.pending && r.task.isNone && r.painted.1 == r.ver && r.shown.isSome then return
    IO.sleep 2
end BidiHost

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/bidi-host"
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
  let sm ← Sim.new
  let s ← App.start sm.io #[1080, 2400, 128, 63, 420] (dir ++ "/quiet.db")
  let counts ← IO.mkRef (0, 0)
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    counts.modify fun (p, f) => if ok then (p+1, f) else (p, f+1)
  let ((), _) ← (show App.M Unit from do
    steps 3
    sm.cmds.modify (·.push "found general")
    steps 5
    if let some pg := (← get).pageNow then
      if let some (b, _) := pg.taps.find? (·.2 == .openChannel 0) then
        sm.cmds.modify (·.push s!"page {b.x + b.w/2} {b.y + b.h/2}")
    steps 3
    check "conversation opens" ((← get).page == .chat)
    for (label, body) in [("hebrew", "א 12:30 ב"), ("arabic", "ا 12:30 ب")] do
      sm.cmds.modify (·.push ("send " ++ body))
      waitIdle sm
      BidiHost.settle
      let s ← get
      let some (_, x) := s.ids[0]? | check "message is listed" false
      let some row := s.rows[x]? | check "message is mounted" false
      let some bmp := row.shown | check "message is painted" false
      check s!"{label}: sent body reaches the painted row" (row.data.text == body && !row.data.pending)
      let line := row.lay.text[0]!
      check s!"{label}: 12:30 glyphs advance left to right" (BidiHost.clockOrder line)
      check s!"{label}: name uses the same number order"
        (BidiHost.clockOrder (Text.oneLine s.font 800 body))
      let xs := (line.filter fun g => BidiHost.clockChars.contains g.c).map (·.x)
      let left := xs.foldl min s.W
      let ref := BidiHost.reference s.font
      check s!"{label}: all {ref.w * ref.h} clock pixels match logical 12:30"
        (BidiHost.stripEq bmp ref (s.dim.textX + left) row.lay.textY)
      writePpm (dir ++ s!"/{label}-row.ppm") bmp.w bmp.rows
      writePpm (dir ++ s!"/{label}-screen.ppm") s.W (← screenOf sm s.W s.Hs s.insetBot)
    pure ()).run s
  let (p, f) ← counts.get
  IO.println s!"bidi headless: pass={p} fail={f}"
  (← IO.getStdout).flush
  IO.Process.exit (if f == 0 then 0 else 1)
