/-
The desktop headless twin: the same Driver, scene, hit dispatch, database
and painter as Linux. Boundary renders, real community switching, settings
navigation, typing/sending, and resize preserving the current community.
-/
import platforms.desktop.Input
import platforms.headless.Sim
import platforms.headless.Hover

open Desktop

private def settle (d : Driver) : IO Driver := do
  let mut d := d
  for _ in [0:30] do
    d ← tick d
    IO.sleep 2
  return d

private def click (d : Driver) (a : Action) : IO Driver := do
  let wanted := if d.ui.switching then (match a with | .community i => Action.popup (.community i) | a => a) else a
  if let some c := (scene d.layout d.height d.ui d.app).find? (·.action == wanted) then
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
  let publication ← d.layers.get
  let vp := scrollViewport d.layout d.height d.ui d.app publication
  check "native viewport is the conversation below the header and above the composer"
    (vp[0]! == 1 && vp[1]!.toNat == d.layout.main.x && vp[2]!.toNat == (App.geom d.app).top &&
      vp[2]!.toNat + vp[4]!.toNat == (App.geom d.app).composerTop &&
      vp[3]!.toNat == d.layout.main.w)
  let drawerUi := { d.ui with context := .settings }
  let drawerLayout := Desktop.zoomLayout d.width true d.dpi
  let covered := scrollViewport drawerLayout d.height drawerUi d.app publication
  check "native scrolling never receives events over the settings drawer"
    (covered[0]! == 1 && covered[1]!.toNat + covered[3]!.toNat == drawerLayout.context.x &&
      covered[3]!.toNat < vp[3]!.toNat)
  let popup := scrollViewport d.layout d.height { d.ui with switching := true } d.app publication
  check "community popup suspends the underlying native viewport" (popup[0]! == 0)
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
  check "widening preserves leaf identity and parent" (d.ui.drawer == .stub && d.ui.stubTitle == "About Quiet" && d.ui.parents.head?.any (·.1 == .you))
  d ← settle (← resize d 390 760)
  check "narrowing preserves the leaf and its back destination" (d.app.page == .stub && d.app.labelText == "About Quiet" && d.app.backStack.head? == some .you)
  d ← settle (← resize d 1100 760)
  d ← click d .close
  check "back after both breakpoint transitions returns to You" (d.ui.drawer == .you && d.ui.context == .settings)
  d ← click d .close
  for (parent, title) in [(App.PageId.communitySettings, "Message retention"),
      (.channelSettings, "Disappearing messages"), (.communitySettings, "Storage on this device"),
      (.communitySettings, "Leave community")] do
    d ← settle (← act d (.page parent))
    d ← settle (← act d (.drawerAct (.stub title)))
    let pg := (drawerPage d.layout d.height d.ui d.app).1
    check s!"{title}: proposed settings have no write controls"
      (pg.taps.all (·.2 == .back) && (if title == "Leave community" then pg.taps.size == 1 else pg.taps.isEmpty))
    d ← settle (← resize d 390 760)
    check s!"{title}: phone keeps the same leaf" (d.app.page == .stub && d.app.labelText == title)
    let (_, s) ← App.back.run d.app
    d ← settle { d with app := s }
    check s!"{title}: phone back returns to its settings context" (d.app.page == parent)
    d ← settle (← resize d 1100 760)
    d ← click d .close
  d ← settle (← act d (.page .communitySettings))
  d ← settle (← act d (.drawerAct (.stub "Leave community")))
  d ← click d (.drawerAct .back)
  check "Stay returns to community settings and retains membership" (d.ui.drawer == .communitySettings && d.app.comms.size == 2)
  d ← click d .close
  d ← click d (.page .chat)
  text.set ("A desktop message", #[17, 17, 17, 17])
  d ← tick d [.text]
  check "native editor reaches app" (d.app.text == "A desktop message")
  d ← click d .send
  check "send stored in active community" (d.app.total == 1 && d.app.text.isEmpty)
  HoverTest.run d
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
        -- Include every pixel right up to the panel edge. A shadow or scrim
        -- on the still-visible conversation must fail this comparison.
        let visibleWidth := if g.context.w > 0 then g.context.x - g.main.x else g.main.w
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
  -- Actual popover interaction over the same database, composer and history.
  d ← settle (← resize { d with ui := {} } 1100 760)
  d ← settle (← act d (.page .chat))
  let basePicture ← picture d
  let beforePopup := d.app.b
  let beforeDraft := d.app.text
  let beforeCommunity := d.app.cur
  d ← click d .switcher
  let m := Switcher.model d.app d.height d.ui.switchOffset
  check "switcher is a 300px popover below the unchanged sidebar head"
    (m.box.x == 8 && m.box.y == 48 && m.box.w == 300 && d.layout.nav.w == 220 && d.ui.switching)
  let rows := (scene d.layout d.height d.ui d.app).filter fun c => match c.action with | .popup (.community _) => true | _ => false
  check "switcher puts the selected acceptance first"
    (rows.head?.any fun c => c.action == .popup (.community ((d.app.comms.findIdx? (·.acc == d.app.cur)).getD 999)))
  let popupPicture ← picture d
  check "popover leaves exposed sidebar and main pixels unchanged"
    ((popupPicture.rows.extract 600 700).map (·.extract 0 800) == (basePicture.rows.extract 600 700).map (·.extract 0 800) &&
     (popupPicture.rows.map (·.extract 1600 4400)) == (basePicture.rows.map (·.extract 1600 4400)))
  let composer := App.composerLayout d.app
  let cx := d.layout.main.x + composer.textX
  let cy := d.height - App.botH d.app + composer.textY + 1
  check "popup excludes composer selection and history scrollbar grabs"
    ((caret d cx cy).isNone && (scrollGrab d (d.width - 4) 200).isNone)
  d ← settle (← wheel d 900 300 1000)
  check "wheel outside popup cannot scroll its conversation" (d.app.b == beforePopup && d.ui.switchOffset == 0)
  d ← settle (← tap d cx cy)
  check "outside click dismisses without changing draft or community"
    (!d.ui.switching && d.app.text == beforeDraft && d.app.cur == beforeCommunity && !d.app.editorFocused)
  d ← click d .settings
  d ← settle (← act d .switcher)
  d ← settle (← act d .close)
  check "Escape dismisses only the topmost popup, preserving underlying settings"
    (!d.ui.switching && d.ui.context == .settings)
  d ← click d .close
  d ← click d .switcher
  d ← click d (.popup .settings)
  check "current community gear opens its settings and dismisses popup"
    (!d.ui.switching && d.ui.drawer == .communitySettings && d.ui.context == .settings && d.app.cur == beforeCommunity)
  d ← click d .close
  d ← click d .switcher
  d ← click d (.popup .invite)
  check "current community invite opens the real Add members flow"
    (!d.ui.switching && d.app.page == .invite && d.app.cur == beforeCommunity && (App.pageIn d.app).link.isSome)
  for (action, page) in [(Switcher.Act.join, App.PageId.joinChoice), (.create, .create)] do
    d ← settle (← act d (.page .chat))
    d ← click d .switcher
    d ← click d (.popup action)
    check s!"popup {repr action} opens its entry flow" (!d.ui.switching && d.app.page == page)
  d ← settle (← act d (.page .chat))
  d ← click d .switcher
  d ← click d (.popup .linked)
  check "Linked devices has an honest destination and closes the popup"
    (!d.ui.switching && d.ui.drawer == .stub && d.ui.stubTitle == "Linked devices")
  d ← click d .close
  -- Long lists use real accepted communities, including equal labels. Every
  -- acceptance remains reachable; scrolling never spills into the messages.
  for i in [0:14] do
    let (_, s) ← (App.found (if i < 2 then "Same community name" else s!"Switcher {i}") "Alex").run d.app
    d ← settle { d with app := s }
  d ← settle (← resize d 1600 600)
  d ← click d .switcher
  let mut seen : List Nat := []
  for _ in [0:30] do
    for c in scene d.layout d.height d.ui d.app do
      if let .popup (.community i) := c.action then seen := i :: seen
    d ← settle (← wheel d 150 250 40)
  check "every real acceptance in a long community list is reachable"
    ((List.range d.app.comms.size).all seen.contains)
  check "long popup reaches its exact scroll limit"
    (d.ui.switchOffset == (Switcher.model d.app d.height 0).contentH - (Switcher.model d.app d.height 0).box.h)
  d ← click d (.popup .linked)
  check "last action remains clickable after scrolling the entire popup"
    (!d.ui.switching && d.ui.stubTitle == "Linked devices")
  d ← click d .close
  for zoomPct in [75, 100, 150, 200] do
    d ← settle (← zoom d zoomPct)
    d ← settle (← act d .switcher)
    let px := d.app.dim.px
    let top := Switcher.model d.app d.height d.ui.switchOffset
    check s!"{zoomPct}% popup respects zoom and window height"
      (top.box.w == px 300 && top.box.y + top.box.h ≤ d.height - px 8 && top.offset == 0)
    let mut offset := 0
    for _ in [0:10] do
      d ← settle (← wheel d (px 150) (px 200) (Int.ofNat (px 180)))
      let m := Switcher.model d.app d.height d.ui.switchOffset
      check s!"{zoomPct}% scroll controls stay inside their visible popup"
        ((scene d.layout d.height d.ui d.app).all fun c =>
          c.pane == .overlay && c.box.x ≥ m.box.x && c.box.x + c.box.w ≤ m.box.x + m.box.w &&
          c.box.y ≥ m.box.y && c.box.y + c.box.h ≤ m.box.y + m.box.h)
      offset := d.ui.switchOffset
    check s!"{zoomPct}% all scrolling is confined to the popup" (offset > 0 && d.app.b == 0)
    d ← settle (← act d .close)
  d ← settle (← zoom d 100)
  d ← click d .switcher
  d ← settle (← resize d 390 760)
  check "narrowing hands the switcher to the existing mobile navigation"
    (!d.ui.switching && d.app.page == .switcher)
  d ← settle (← resize d 1280 760)
  check "widening returns to the desktop popover over the same community"
    (d.ui.switching && d.app.page == .chat)
  let same := (d.app.comms.toList.zipIdx).filter fun (c, _) => c.name == "Same community name"
  check "fixture contains two distinct acceptances with identical labels" (same.length == 2 && same[0]!.1.acc != same[1]!.1.acc)
  for (community, i) in same do
    d ← settle (← act d .close)
    d ← click d .switcher
    for _ in [0:20] do
      if (scene d.layout d.height d.ui d.app).any (·.action == .popup (.community i)) then break
      d ← settle (← wheel d 150 250 52)
    d ← click d (.popup (.community i))
    check "identical displayed names still select their own acceptance" (d.app.cur == community.acc && !d.ui.switching)
  d ← click d .switcher
  let some c := (scene d.layout d.height d.ui d.app).find? (fun c => match c.action with | .popup (.community _) => true | _ => false)
    | throw (IO.userError "missing current community")
  let selected := d.app.cur
  d ← settle (← tap d (c.box.x + c.box.w / 2) (c.box.y + c.box.h / 2) true)
  check "long press exposes the full label without switching community"
    (!d.ui.switching && d.app.page == .label && d.app.labelText == "Same community name" && d.app.cur == selected)
  IO.println s!"desktop: {← checks.get} checks; 27 renders"
  (← IO.getStdout).flush
  IO.Process.exit 0

def main (args : List String) : IO UInt32 := do
  try suite args
  catch e => IO.eprintln s!"{e}"; IO.Process.exit 1
