/-
The desktop headless twin: the same Driver, scene, hit dispatch, database
and painter as Linux. Boundary renders, real community switching, settings
navigation, typing/sending, and resize preserving the current community.
-/
import platforms.desktop.Input
import platforms.headless.Sim

open Desktop

private def settle (d : Driver) : IO Driver := do
  let mut d := d
  for _ in [0:30] do
    d ← tick d
    IO.sleep 2
  return d

private def click (d : Driver) (a : Action) : IO Driver := do
  let some c := (scene d.layout d.height d.ui d.app).find? (·.action == a)
    | throw (IO.userError s!"no drawn control {repr a}")
  settle (← tap d (c.box.x + c.box.w / 2) (c.box.y + c.box.h / 2))

private def suite (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/desktop"
  IO.FS.createDirAll dir
  let db := dir ++ "/test.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (db ++ suffix) then IO.FS.removeFile (db ++ suffix)
  let sm ← Sim.new
  let text ← IO.mkRef ("", #[0, 0, 0, 0])
  let io := { sm.io with text := text.get, setText := fun t => let n := t.length.toUInt32; text.set (t, #[n, n, n, n]) }
  let mut d ← start io 1100 760 db
  let checks ← IO.mkRef 0
  let check (name : String) (ok : Bool) := do
    unless ok do throw (IO.userError s!"FAIL {name}")
    checks.modify (· + 1)
    IO.println s!"ok {name}"
    (← IO.getStdout).flush
  let mobileFont ← Font.load "assets/font.bin" 160
  let fontSample (font : Font.Font) :=
    (Paint.Bitmap.blank 320 48 (Paint.solid Row.bg 320)).line font
      (Text.oneLine font 320 "Quiet שלום 日本語 🙂") 0 0 Row.nameInk
  check "desktop paints the same Noto and emoji as the mobile renderer at logical density"
    (!d.app.font.noto.chars.isEmpty && (fontSample d.app.font).rows == (fontSample mobileFont).rows)
  for name in ["Quiet", "Garden"] do
    let (_, s) ← (App.found name "Alex").run d.app
    d ← settle { d with app := s }
  check "two actual accepted communities" (d.app.comms.size == 2)
  d ← click d .switcher
  d ← click d (.community 0)
  check "switch by drawn acceptance" (d.app.cur == d.app.comms[0]!.acc && d.app.page == .chat)
  let first := d.app.cur
  text.set ("Unsent in first community", #[0, 0, 0, 0])
  d ← tick d [.text]
  d ← click d .switcher
  d ← click d (.community 1)
  check "switch to distinct community" (d.app.cur != first && d.app.cur == d.app.comms[1]!.acc)
  check "switch clears editor and old draft" (d.app.text.isEmpty && (← text.get).1.isEmpty)
  d ← click d .settings
  check "settings opens three panes" (d.layout.count == 3 && d.ui.context == .settings)
  d ← click d (.page .requests)
  check "settings uses real requests page" (d.app.page == .requests && d.ui.context == .closed)
  d ← click d (.page .chat)
  text.set ("A desktop message", #[17, 17, 17, 17])
  d ← tick d [.text]
  check "native editor reaches app" (d.app.text == "A desktop message")
  d ← click d .send
  check "send stored in active community" (d.app.total == 1 && d.app.text.isEmpty)
  text.set ("Keep this draft", #[4, 9, 9, 9])
  d ← tick d [.text]
  d ← settle (← resize d 770 480)
  check "resize keeps draft and selection" (d.app.text == "Keep this draft" && d.app.sel == #[4, 9, 9, 9])
  check "resize updates actual row width" (d.app.W == 550 && d.app.rows.size > 0)
  check "resize repaints cached rows" (d.app.rows.toArray.all fun (_, r) => r.shown.any (·.w == d.app.W))
  let cy := d.height - App.botH d.app + 12
  check "composer drag starts at first codepoint" (caret d (d.layout.main.x + 16) cy == some 0)
  check "sidebar cannot select composer text" ((caret d 10 cy).isNone)
  -- Independent expected tracks, transcribed from CSS (reference.json).
  let cases := #[(320, 0, 320, 0, 0, 0, 320), (719, 0, 719, 0, 0, 0, 719),
    (720, 220, 500, 0, 0, 0, 720), (769, 220, 549, 0, 0, 0, 769),
    (770, 220, 550, 0, 220, 275, 275), (800, 220, 580, 0, 220, 275, 305),
    (869, 220, 649, 0, 220, 275, 374), (870, 220, 650, 0, 220, 275, 375),
    (1440, 220, 1220, 0, 220, 845, 375)]
  let mut manifest := ""
  for (w, l, m, r, lo, mo, ro) in cases do
    for ctx in [Context.closed, .settings, .threads] do
      d ← settle (← resize { d with ui := { d.ui with context := ctx } } w 760)
      let g := d.layout
      let (el, em, er) := if ctx == .closed then (l, m, r) else (lo, mo, ro)
      check s!"tracks {w} {repr ctx}" (g.nav.w == el && g.main.w == em && g.context.w == er)
      let cs := scene g d.height d.ui d.app
      check s!"controls {w} {repr ctx}" (!cs.isEmpty && cs.all fun c =>
        decide (Fits g d.height c.pane c.box) && (hit cs (c.box.x + c.box.w / 2) (c.box.y + c.box.h / 2)).isSome)
      let pic ← picture d
      check s!"frame {w} {repr ctx}" (pic.w == w && pic.h == 760 && pic.rows.all (·.size == w * 4))
      let tag := s!"{w}-{if ctx == .closed then "chat" else if ctx == .settings then "settings" else "threads"}"
      writePpm (dir ++ "/" ++ tag ++ ".ppm") pic.w pic.rows
      manifest := manifest ++ s!"{tag} {g.nav.w} {g.main.w} {g.context.w}\n"
  IO.FS.writeFile (dir ++ "/frames.txt") manifest
  -- a resize never flashes rows to placeholders (settleFrame, settled_no_hold):
  -- a conversation taller than the window, then one frame after each
  -- resize, every row it shows is painted and no placeholder is drawn
  d ← settle (← resize { d with ui := { d.ui with context := .closed } } 1100 760)
  for i in [0:40] do
    let (_, s) ← (App.sendText s!"Message {i}: a desktop resize shows every row painted, never a placeholder").run d.app
    d := { d with app := s }
  for _ in [0:20] do
    if d.app.total ≥ 41 then break
    d ← settle d
  check s!"a conversation taller than the window ({d.app.total} messages)" (d.app.total ≥ 41)
  sm.b.set 800
  d ← settle d
  let anchor := App.captureAnchor d.app
  check "desktop resize has a nonempty message anchor" anchor.isSome
  let mut unpainted := 0
  let mut flashes := 0
  for (w, h) in [(1040, 760), (980, 700), (900, 760), (771, 640), (1300, 900), (1440, 760), (1100, 760)] do
    d ← tick (← resize d w h)
    check s!"{w}x{h}: desktop resize preserves the message anchor" (App.captureAnchor d.app == anchor)
    unless framePainted d.app do unpainted := unpainted + 1
    -- a placeholder's bar (App.holdLine): its colour from pad + 48 dp on
    let pic ← picture d
    let x0 := d.layout.main.x + d.app.dim.pad + d.app.dim.px 48
    let bars := (List.range (h - App.botH d.app - 40 - App.topH d.app)).filter fun k =>
      (List.range 40).all fun i => Paint.getPx pic.rows[40 + App.topH d.app + k]! (x0 + i) == Row.placeholder
    unless bars.isEmpty do flashes := flashes + 1
  check s!"one frame after each of 7 resizes, no row shows a placeholder ({flashes} did)" (flashes == 0)
  check s!"one frame after each of 7 resizes, every row it shows painted ({unpainted} not)" (unpainted == 0)
  IO.println s!"desktop: {← checks.get} checks; 27 renders"
  (← IO.getStdout).flush
  IO.Process.exit 0

def main (args : List String) : IO UInt32 := do
  try suite args
  catch e => IO.eprintln s!"{e}"; IO.Process.exit 1
