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
  if let some c := (scene d.layout d.height d.ui d.app).find? (·.action == a) then
    return ← settle (← tap d (c.box.x + c.box.w / 2) (c.box.y + c.box.h / 2))
  let c : Composer.Layout := App.composerLayout d.app
  let box : Option Composer.Box := match a with
    | .send => some c.send
    | .photos => (c.deck.find? (fun (entry : Composer.Box × Composer.Hit) => entry.2 == Composer.Hit.addPhotos)).map (fun (entry : Composer.Box × Composer.Hit) => entry.1)
    | _ => none
  let some box := box | throw (IO.userError s!"no drawn control {repr a}")
  settle (← tap d (d.layout.main.x + box.x + box.w / 2)
    (d.height - App.botH d.app + box.y + box.h / 2))

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
  check "new community starts with its own empty draft" (d.app.text.isEmpty && (← text.get).1.isEmpty)
  d ← click d .switcher
  d ← click d (.community 0)
  check "returning to community restores its draft" (d.app.cur == first && d.app.text == "Unsent in first community")
  d ← click d .switcher
  d ← click d (.community 1)
  d ← click d .settings
  check "settings opens three panes" (d.layout.count == 3 && d.ui.context == .settings)
  let conversationWidth := d.app.W
  d ← click d (.drawerAct .appearance)
  check "settings uses real appearance page without replacing conversation" (d.ui.drawer == .appearance && d.app.page == .chat)
  check "settings preserves conversation width" (d.app.W == conversationWidth)
  d ← click d (.drawerAct (.theme .dark))
  check "drawer theme control changes the actual app" (d.app.theme.setting == .dark)
  d ← click d (.drawerAct (.theme .light))
  d ← click d .close
  check "settings back returns to You" (d.ui.drawer == .you && d.ui.context == .settings)
  d ← click d .close
  -- Reach the last settings row in a short window using the real wheel,
  -- hit dispatch and page stack; the conversation must not move behind it.
  d ← settle (← resize d 1000 480)
  d ← click d .settings
  let before := d.app.b
  d ← settle (← wheel d 900 300 10000)
  check "drawer wheel scrolls only its own viewport" (d.ui.offset > 0 && d.app.b == before)
  d ← click d (.drawerAct (.stub "About Quiet"))
  check "scrolled drawer row opens its child" (d.ui.drawer == .stub && d.ui.stubTitle == "About Quiet")
  d ← click d .close
  check "drawer child back resets the parent scroll" (d.ui.drawer == .you && d.ui.offset == 0)
  d ← click d .close
  d ← settle (← resize d 390 480)
  d ← settle (← act d (.page .you))
  check "phone settings starts at the top" (d.app.page == .you && d.app.b == App.scrollHeight d.app - App.viewH d.app)
  let initial ← picture d
  d ← settle (← wheel d 200 300 10000)
  let scrolled ← picture d
  check "phone settings scrolls real page pixels" (d.app.b == 0 && initial.rows != scrolled.rows)
  let some pg := d.app.pageNow | throw (IO.userError "missing phone settings")
  let some (box, _) := pg.taps.find? (·.2 == .stub "About Quiet") | throw (IO.userError "missing About row")
  let top := pg.bmp.h - App.viewH d.app - d.app.b
  d ← settle (← tap d (box.x + box.w / 2) (App.topH d.app + box.y - top + box.h / 2))
  check "phone scrolled row dispatches to the visible child" (d.app.page == .stub && d.app.labelText == "About Quiet")
  d ← settle (← resize d 1100 760)
  d ← click d .close
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
  let compose := App.composerLayout d.app
  let cy := d.height - App.botH d.app + compose.textY + 1
  check "composer drag starts at first codepoint" (caret d (d.layout.main.x + compose.textX) cy == some 0)
  check "sidebar cannot select composer text" ((caret d 10 cy).isNone)
  -- Boundary cases accompany the independently rendered libquiet pixel
  -- fixtures in tests/visual; context width does not subtract from main.
  let cases := #[(320, 0, 320, 0, 0, 320, 0), (719, 0, 719, 0, 0, 719, 0),
    (720, 220, 500, 0, 220, 500, 375), (769, 220, 549, 0, 220, 549, 375),
    (770, 220, 550, 0, 220, 550, 375), (800, 220, 580, 0, 220, 580, 375),
    (869, 220, 649, 0, 220, 649, 375), (870, 220, 650, 0, 220, 650, 375),
    (1440, 220, 1220, 0, 220, 1220, 375)]
  let mut manifest := ""
  for (w, l, m, r, lo, mo, ro) in cases do
    for ctx in [Context.closed, .settings, .threads] do
      d ← resize { d with ui := { d.ui with context := .closed } } w 760
      d ← act d (.page .chat)
      d ← if ctx == .settings then act d (.page .you) else if ctx == .threads then act d .threads else pure d
      d ← settle d
      let g := d.layout
      let (el, em, er) := if ctx == .closed then (l, m, r) else (lo, mo, ro)
      check s!"tracks {w} {repr ctx}" (g.nav.w == el && g.main.w == em && g.context.w == er)
      let cs := scene g d.height d.ui d.app
      check s!"controls {w} {repr ctx}" ((if g.nav.w == 0 && g.context.w == 0 then cs.isEmpty else !cs.isEmpty) && cs.all fun c =>
        decide (Fits g d.height c.pane c.box) && (hit cs (c.box.x + c.box.w / 2) (c.box.y + c.box.h / 2)).isSome)
      let pic ← picture d
      check s!"frame {w} {repr ctx}" (pic.w == w && pic.h == 760 && pic.rows.all (·.size == w * 4))
      if g.main.w > 0 then
        let ls ← d.layers.get
        let expected := Translate.compose ls.placement (ls.placement[15]?.getD 0).toInt32 d.height
          d.app.bgRow ls.list ls.top ls.bot ls.hold
        let visibleWidth := if g.context.w > 0 then g.context.x - g.main.x - 24 else g.main.w
        let actual := pic.rows.map fun row => row.extract (4*g.main.x) (4*(g.main.x+visibleWidth))
        let expected := expected.map (·.extract 0 (4*visibleWidth))
        check s!"{w}/{repr ctx}: every content pixel matches the shared mobile frame" (actual == expected)
        check s!"{w}/{repr ctx}: shared composer buttons fit without overlap" (Id.run do
          let c : Composer.Layout := App.composerLayout d.app
          let boxes := (c.deck.map (·.1)).push c.send
          return boxes.all (fun b => b.w ≥ 24 && b.x+b.w ≤ d.app.W) &&
            (Array.range boxes.size).all fun i => (Array.range boxes.size).all fun j =>
              i == j || boxes[i]!.x+boxes[i]!.w ≤ boxes[j]!.x || boxes[j]!.x+boxes[j]!.w ≤ boxes[i]!.x)
        let chips := Composer.layout (App.composerFont d.app) d.app.dim d.app.W "" 4 d.app.wide d.app.mobile
        check s!"{w}/{repr ctx}: four photo chips remain reachable" (chips.chips.all fun (b,x) =>
          b.x+b.w ≤ d.app.W && b.y+b.h ≤ chips.h && x.x+x.w ≤ d.app.W && x.y+x.h ≤ chips.h)
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
  sm.b.set 0
  d ← settle d
  let some bar := scrollbar d.layout d.app | throw (IO.userError "missing scrollbar for long conversation")
  check "scrollbar pinned to newest at bottom" (bar.thumb.y + bar.thumb.h == bar.track.y + bar.track.h)
  let image ← picture d
  check "scrollbar thumb is visible in the composed frame"
    (Paint.getPx image.rows[bar.thumb.y + bar.thumb.h / 2]! (bar.thumb.x + 2) == Palette.color d.app.dim.theme .muted)
  let grab := scrollGrab d (bar.thumb.x + 2) (bar.thumb.y + bar.thumb.h / 2)
  check "thumb accepts pointer down; message area does not" (grab.isSome && (scrollGrab d (d.layout.main.x + 40) bar.thumb.y).isNone)
  scrollDrag d (grab.getD 0) bar.track.y
  d ← settle d
  check "drag thumb to top reaches oldest history" (d.app.b > 0 && d.app.b == (App.bottoms d.app).2 - (App.geom d.app).viewNow)
  scrollDrag d (grab.getD 0) (bar.track.y + bar.track.h + 100)
  d ← settle d
  check "drag beyond bottom returns to newest" (d.app.b == 0)
  check "short conversation has no scrollbar" ((Scrollbar.layout 390 56 600 500 0).isNone)
  let hidden := { d with ui := { d.ui with context := .settings }, width := 390 }
  check "full-width context has no conversation scrollbar" ((scrollbar hidden.layout hidden.app).isNone)
  sm.b.set 800
  d ← settle d
  let anchor := App.captureAnchor d.app
  check "desktop resize has a nonempty message anchor" anchor.isSome
  let mut unpainted := 0
  let mut flashes := 0
  for (w, h) in [(1040, 760), (719, 700), (720, 760), (390, 844), (770, 640), (1440, 760), (1100, 760)] do
    d ← tick (← resize d w h)
    check s!"{w}x{h}: desktop resize preserves the message anchor" (App.captureAnchor d.app == anchor)
    unless framePainted d.app do unpainted := unpainted + 1
    -- a placeholder's bar (App.holdLine): its colour from pad + 48 dp on
    let pic ← picture d
    let x0 := d.layout.main.x + d.app.dim.pad + d.app.dim.px 48
    let bars := (List.range (h - App.botH d.app - App.topH d.app)).filter fun k =>
      (List.range 40).all fun i => Paint.getPx pic.rows[App.topH d.app + k]! (x0 + i) == Palette.color d.app.dim.theme .selected
    unless bars.isEmpty do flashes := flashes + 1
  check s!"one frame after each of 7 resizes, no row shows a placeholder ({flashes} did)" (flashes == 0)
  check s!"one frame after each of 7 resizes, every row it shows painted ({unpainted} not)" (unpainted == 0)
  IO.println s!"desktop: {← checks.get} checks; 27 renders"
  (← IO.getStdout).flush
  IO.Process.exit 0

def main (args : List String) : IO UInt32 := do
  try suite args
  catch e => IO.eprintln s!"{e}"; IO.Process.exit 1
