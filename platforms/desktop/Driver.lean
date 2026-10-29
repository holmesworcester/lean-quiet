/-
Responsive desktop composition of the phone app. The app still runs
App.step on its real database, writer and views. Its three layers feed
the desktop root; resize invalidates width-dependent row/page caches.
The platform supplies logical pixels and does only the final scale/blit.

A frame at a new size is shown only once the rows it shows are painted
at that size (`settleFrame`): a resize never flashes rows to placeholders
(Desktop.settled_no_hold).
-/
import platforms.desktop.View

namespace Desktop

structure Driver where
  app : App.St
  ui : Ui := {}
  width : Nat
  height : Nat
  dpi : Nat := 160
  requestedZoom : Nat := 100
  layers : IO.Ref Layers
  screen : IO.Ref (Array UInt32)
  /-- The app's size (W, Hs) in the frame last settled. -/
  settled : Nat × Nat := (0, 0)

def Driver.layout (d : Driver) : Layout := Desktop.zoomLayout d.width (d.ui.context != .closed) d.dpi

def start (base : App.Io) (w h : Nat) (path : String)
    (net : Option (Nat × Bool) := none) : IO Driver := do
  let ls ← IO.mkRef ({} : Layers)
  let g := Desktop.layout w false
  let sc ← IO.mkRef #[g.main.w.toUInt32, h.toUInt32, 0, 0, 160, (← base.screen)[5]?.getD 0]
  let io := { base with
    screen := do return (← sc.get).set! 5 ((← base.screen)[5]?.getD 0)
    frame := fun fr _ o top bot _ placement hold => do
      ls.set ⟨fr, top, bot, o.toNat, placement, hold⟩
      return #[] }
  let s ← App.start io (← sc.get) path net
  -- Use the app's density-scaled font, including Noto and colour emoji.
  -- Replacing it with the old reduced bitmap discards the shared renderer.
  let font := s.font.atSize (if w ≥ 720 then 14 else 15)
  let s := { s with wide := w ≥ 720, mobile := false, font, dim := { s.dim with cell := font.cell } }
  return { app := App.themed s s.theme, width := w, height := h, layers := ls, screen := sc }

def resize (d : Driver) (w h : Nat) : IO Driver := do
  let w := max 320 w
  let h := max 480 h
  let dpi := max 80 (min (d.requestedZoom * 160 / 100) (min (w * 160 / 320) (h * 160 / 240)))
  let mut d := { d with width := w, height := h, dpi }
  if w < ((720 * d.dpi + 80) / 160) && d.ui.context != .closed then
    let (_, s) ← (do
      for (parent, _) in d.ui.parents.reverse do App.openPage parent
      App.openPage d.ui.drawer).run { d.app with labelText := d.ui.stubTitle }
    d := { d with app := s, ui := { d.ui with context := .closed } }
  if w ≥ ((720 * d.dpi + 80) / 160) && d.app.page.drawer then
    let viewPage := d.app.page
    let parents := (d.app.backStack.takeWhile App.PageId.drawer).map fun p =>
      (p, ((d.ui.parents.find? (·.1 == p)).map (·.2)).getD "")
    let (_, s) ← (App.openPage .chat).run d.app
    d := { d with app := s, ui := { d.ui with context := .settings, drawer := viewPage, parents, stubTitle := d.app.labelText } }
  d := { d with app := { d.app with wide := w ≥ ((720 * d.dpi + 80) / 160) } }
  let g := d.layout
  let aw := max ((275 * d.dpi + 80) / 160) g.main.w
  let ah := d.height
  d.screen.set #[aw.toUInt32, ah.toUInt32, 0, 0, d.dpi.toUInt32, (← d.screen.get)[5]?.getD 0]
  let (_, s) ← (App.resize (← d.screen.get)).run d.app
  return { d with app := s }

/-- Browser zoom changes CSS density, never the native window size. Width-
dependent content and glyph raster caches are retired by App.resize. -/
def zoom (d : Driver) (percent : Nat) : IO Driver := do
  let percent := max 50 (min 200 percent)
  -- Below a 320 x 240 CSS viewport, keep controls reachable rather than
  -- allowing fixed chrome to consume the entire window.
  let d ← resize { d with requestedZoom := percent, settled := (0, 0), ui := { d.ui with offset := 0 } } d.width d.height
  return d

def act (d : Driver) (a : Action) : IO Driver := do
  let blurs := match a with | .settings | .threads | .page _ | .drawerAct _ => true | _ => false
  if blurs then d.app.io.ime false
  let d := if blurs then { d with app := { d.app with editorFocused := false, chromeKey := "" } } else d
  match a with
  | .settings => return { d with ui := { d.ui with context := .settings, drawer := .you, parents := [], offset := 0 } }
  | .threads => return { d with ui := { d.ui with context := .threads, drawer := .stub, stubTitle := "Threads", parents := [], offset := 0 } }
  | .close | .drawerAct .back =>
    match d.ui.parents with
    | (parent, title) :: rest => return { d with ui := { d.ui with drawer := parent, stubTitle := title, parents := rest, offset := 0 } }
    | [] => return { d with ui := { d.ui with context := .closed } }
  | .previous => return { d with ui := { d.ui with first := d.ui.first - (d.height - d.app.dim.px 180) / max 1 (d.app.dim.px 36) } }
  | .next =>
    let n := (d.height - d.app.dim.px 180) / max 1 (d.app.dim.px 36)
    return { d with ui := { d.ui with first := if d.ui.first + n < d.app.comms.size then d.ui.first + n else d.ui.first } }
  | .switcher =>
    if d.layout.nav.w > 0 then return { d with ui := { d.ui with switching := !d.ui.switching } }
    let (_, s) ← (App.openPage .switcher).run d.app
    return { d with app := s }
  | .community i =>
    let (_, s) ← (do App.switchTo i; App.openPage .chat).run d.app
    return { d with app := s, ui := { d.ui with switching := false } }
  | .send =>
    let (_, s) ← App.sendNow.run d.app
    return { d with app := s }
  | .photos =>
    let (_, s) ← App.attachPhoto.run d.app
    return { d with app := s }
  | .page p =>
    if p.drawer && d.width ≥ ((720 * d.dpi + 80) / 160) then
      let (_, s) ← (if d.app.page == .home then App.openPage .chat else pure ()).run d.app
      return { d with app := s, ui := { d.ui with context := .settings, drawer := p, parents := [], offset := 0, switching := false } }
    let (_, s) ← (App.openPage (if p == .home && d.width ≥ ((720 * d.dpi + 80) / 160) then .chat else p)).run d.app
    return { d with app := s, ui := { d.ui with context := .closed, switching := false } }
  | .drawerAct action =>
    let target : Option App.PageId := match action with
      | .appearance => some .appearance | .you => some .you
      | .communitySettings => some .communitySettings | .channelSettings => some .channelSettings
      | .stub _ => some .stub | _ => none
    if let some target := target then
      let title := match action with | .stub title => title | _ => ""
      return { d with ui := { d.ui with
        context := .settings, drawer := target, stubTitle := title, offset := 0,
        parents := if d.ui.context == .closed then [] else (d.ui.drawer, d.ui.stubTitle) :: d.ui.parents } }
    let (_, s) ← (App.onPageAct action).run d.app
    let stay := match action with | .theme _ => true | _ => false
    return { d with app := s, ui := { d.ui with context := if stay then d.ui.context else .closed } }

def tap (d : Driver) (x y : Nat) (long := false) : IO Driver := do
  let g := d.layout
  if let some c := hit (scene g d.height d.ui d.app) x y then return ← act d c.action
  if g.context.w > 0 && x ≥ g.context.x then return d
  if x < g.main.x || x ≥ g.main.x + g.main.w || y ≥ d.height then return d
  let x := x - g.main.x
  let s := d.app
  let bh := App.botH s
  let th := App.topH s
  let (r, py) := if y < th then (App.Region.header, y)
    else if y ≥ s.Hs - bh then (.composer, y - (s.Hs - bh))
    else (.list, (if s.page == .chat || s.page.drawer then s.b else 0) + s.Hs - bh - 1 - y)
  let (_, s) ← (App.onTap r x py long).run s
  return { d with app := s }

/-- Wheel events belong to the topmost visible scroll viewport. A drawer
never scrolls the covered conversation. Positive delta means down the page. -/
def wheel (d : Driver) (x y : Nat) (delta : Int) : IO Driver := do
  let g := d.layout
  if g.context.w > 0 && x ≥ g.context.x then
    if y < d.app.dim.px 60 then return d
    let maxOffset := (drawerPage g d.height d.ui d.app).1.bmp.h - (d.height - d.app.dim.px 60)
    return { d with ui := { d.ui with offset := min maxOffset (Int.ofNat d.ui.offset + delta).toNat } }
  if x ≥ g.main.x && x < g.main.x + g.main.w && y ≥ App.topH d.app &&
      y < d.height - App.botH d.app && (d.app.page == .chat || d.app.page.drawer) then
    d.app.io.scrollBy (-delta).toFloat
  return d

/-- Sidebar and drawer are independent mounted query roots. They declare
through App.query, then join the conversation in one frame publication. -/
def observe (d : Driver) : App.M Unit := do
  modify fun s => { s with queryNeeds := #[], querySeen := {} }
  let s ← get
  if s.me.c.isEmpty then return
  if d.layout.nav.w > 0 then
    let owner := ["sidebar".toUTF8, s.cur]
    let (name, _) ← Component.author ⟨owner ++ ["you".toUTF8], true⟩ s.me.c s.me.user (s.ownName, false)
    modify fun s => { s with ownName := name }
    if let some (.members members _) ← App.query ⟨owner ++ ["people".toUTF8], true⟩ (.members s.me.c s.me.user) then
      let ordered := members.filter (·.1 == s.me.user) ++ members.filter (·.1 != s.me.user)
      let mut names := #[]
      for i in [0:ordered.size] do
        let (id, _, _) := ordered[i]!
        let old := ((s.memberIds.findIdx? (· == id)).bind fun j => s.members[j]?).map (·.1) |>.getD "…"
        let name ← if s.dim.px 186 + (i + 1) * s.dim.px 30 ≤ d.height - s.dim.px 48 then
          pure (← Component.author ⟨owner ++ ["author".toUTF8, id], true⟩ s.me.c id (old, false)).1
          else pure old
        names := names.push (name, id == s.me.user)
      modify fun s => { s with members := names, memberIds := ordered.map (·.1) }
  if d.ui.context != .closed then
    App.observeSettings ["drawer".toUTF8, s.cur] (d.ui.drawer == .you)
      (d.ui.drawer == .communitySettings || d.ui.drawer == .channelSettings)

def stepApp (d : Driver) (events : List App.Event := []) : IO Driver := do
  let action : App.M Unit := do
    if d.width ≥ ((720 * d.dpi + 80) / 160) && (← get).page == .home then App.openPage .chat
    observe d
    let roots := (← get).queryNeeds
    discard <| App.step events roots
  let (_, s) ← action.run d.app
  return { d with app := s }

/-- Every row the list frame shows is painted at its own height, with
no paint of it in flight; on a page, there is no list frame. The frame
then shows no row's placeholder (`settled_no_hold`). -/
def framePainted (s : App.St) : Bool :=
  let (i0, slice, _) := App.frameSlice s s.b (App.bottoms s).1
  s.page != .chat || (slice.all (fun r => r.2 == some r.1) &&
    (List.range slice.size).all fun j =>
      match s.ids[i0 + j]? with
      | some (_, x) => (s.rows[x]?.map (·.task.isNone)).getD true
      | none => true)

/-- After the app's size changed, steps of the app until every row its
frame shows is painted at the new size, with every picture decoded
before the step that painted it; at most 50 steps, 2 ms apart. -/
def settleFrame (d : Driver) : IO Driver := do
  let mut d := d
  -- whether every picture was decoded before the last step began, so
  -- that step painted its rows with them
  let mut decoded := false
  for _ in [0:50] do
    if decoded && framePainted d.app then break
    IO.sleep 2
    decoded ← d.app.imgs.toList.allM fun (_, t) => IO.hasFinished t.result
    d ← stepApp d
  return { d with settled := (d.app.W, d.app.Hs) }

def tick (d : Driver) (events : List App.Event := []) : IO Driver := do
  let d ← resize d d.width d.height
  let d ← stepApp d events
  if (d.app.W, d.app.Hs) != d.settled then settleFrame d else return d

def picture (d : Driver) : IO Paint.Bitmap := do
  return paint d.layout d.height d.ui d.app (← d.layers.get)

end Desktop
