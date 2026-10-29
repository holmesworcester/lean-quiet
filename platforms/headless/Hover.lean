/- Real desktop transitions and pixels, including component paint, the query
and raster pools, and the overhanging message toolbar. Run by host:desktop. -/
import platforms.desktop.Input

namespace Desktop.HoverTest

private def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError ("hover: " ++ label))
  IO.println ("ok hover: " ++ label)

def run (initial : Driver) : IO Unit := do
  let d := pointerEvent { initial with ui := {} } .leave
  let rest ← picture d
  let hot := pointerEvent d (.motion 100 28)
  let hovered ← picture hot
  check "native motion paints the community button" (rest.rows != hovered.rows && cursor hot == 1)
  for e in [Hover.Event.leave, .blur, .touch] do
    let cleared := pointerEvent hot e
    check s!"{repr e} restores every resting pixel" ((← picture cleared).rows == rest.rows && cursor cleared == 0)
  let popup ← act hot .switcher
  check "popup blocks both underlying panes" ((pointer popup.layout popup.height popup.ui .nav).isNone && (pointer popup.layout popup.height popup.ui .main).isNone)
  let outside := pointerEvent popup (.motion (d.layout.main.x + 100) 500)
  check "empty popup dismiss surface cannot show an underlying hand" (cursor outside == 0)
  let settings ← act d .settings
  let pg := (drawerPage settings.layout settings.height settings.ui settings.app).1
  let some (box, _) := pg.taps.find? (·.2 == .appearance) | throw (IO.userError "missing Appearance target")
  let hot := pointerEvent settings (.motion (settings.layout.context.x + box.x + 20) (60 + box.y + box.h/2))
  let a ← picture settings
  let b ← picture hot
  check "settings hover paints through the actual drawer" (a.rows != b.rows && cursor hot == 1)
  check "settings hover leaves every uncovered conversation pixel unchanged"
    (a.rows.map (·.extract (d.layout.main.x*4) (settings.layout.context.x*4)) == b.rows.map (·.extract (d.layout.main.x*4) (settings.layout.context.x*4)))
  for theme in [Theme.Value.light, .dark] do
    let dm : Row.Dim := { dpi := 160, cell := 14, theme }
    let bg := Paint.Bitmap.blank 375 100 (Paint.solid (Palette.color theme .panel) 375)
    let item : Appearance.Item := { text := "Unavailable", action := .none, disabled := true }
    let a := (Appearance.item d.app.font dm bg 0 item).1
    let b := (Appearance.item d.app.font { dm with hover := some (20, 20) } bg 0 item).1
    check s!"disabled settings retain pixels in {repr theme}" (a.rows == b.rows)
    let inactive := (Pages.rows d.app.font dm bg 0 #[("", "Unavailable", Pages.Act.none)]).1
    let attempted := (Pages.rows d.app.font { dm with hover := some (30, 20) } bg 0 #[("", "Unavailable", Pages.Act.none)]).1
    check s!"disabled shared page rows retain pixels in {repr theme}" (inactive.rows == attempted.rows)
    let item := { item with disabled := false, action := .appearance }
    let a := (Appearance.item d.app.font dm bg 0 item).1
    let b := (Appearance.item d.app.font { dm with hover := some (20, 20) } bg 0 item).1
    check s!"enabled settings use Gray 06 in {repr theme}" (a.rows != b.rows && Paint.getPx b.rows[5]! 5 == Palette.color theme .selected)
  let c := App.composerLayout d.app
  let cy := d.height - App.botH d.app
  check "composer asks OS for text cursor" (cursor (pointerEvent d (.motion (d.layout.main.x+c.textX+4) (cy+c.textY+4))) == 2)
  check "empty send remains disabled" (cursor (pointerEvent d (.motion (d.layout.main.x+c.send.x+c.send.w/2) (cy+c.send.y+c.send.h/2))) == 0)
  let some (_, id) := d.app.ids[0]? | throw (IO.userError "hover fixture needs a message")
  let some top := messageTop d.app d.height id | throw (IO.userError "missing row position")
  let x := d.layout.main.x + 80
  let y := max (App.topH d.app) top.toNat + 20
  let authorX := d.layout.main.x + d.app.dim.pad + d.app.dim.avatar/2
  let authorY := top.toNat + Row.headY d.app.dim ((d.app.rows[id]?).map (·.data) |>.getD default) + d.app.dim.px 20
  let author := pointerEvent d (.motion authorX authorY)
  check "message author uses a native hand cursor" (cursor author == 1)
  let profile ← tap author authorX authorY
  check "author opens the profile of the signed message author" (profile.app.profileOf.any (fun (user, _, _) => user == d.app.me.user))
  let hot := pointerEvent d (.motion x y)
  check "message under pointer owns hover" ((hoveredRow hot.layout hot.height hot.ui hot.app).any (·.1 == id))
  let reads := d.app.queryReads
  let paints := d.app.paints
  let before ← d.app.raster.stats
  let image ← picture hot
  check "message hover changes pixels" (image.rows != rest.rows)
  let some cache ← d.hoverCache.get | throw (IO.userError "no hover paint cached")
  let moved := pointerEvent hot (.motion (x+8) (y+1))
  discard <| picture moved
  let some cached ← d.hoverCache.get | throw (IO.userError "hover cache lost")
  check "motion within row reuses the same painted inputs" (cache.1 == cached.1 && cache.2.rows == cached.2.rows)
  let after ← d.app.raster.stats
  check "hover does not schedule queries or raster work" (d.app.queryReads == reads && d.app.paints == paints && (before.started, before.steps, before.completed, before.cancelled) == (after.started, after.steps, after.completed, after.cancelled))
  let some bar := messageBar d.layout d.height d.app id | throw (IO.userError "missing message toolbar")
  let padding := pointerEvent hot (.motion (bar.x+2) (bar.y+24))
  check "toolbar padding has no enabled action or hand cursor" ((messageAction d.layout d.height padding.ui d.app (bar.x+2) (bar.y+24)).isNone && cursor padding == 0)
  let diagonal := pointerEvent hot (.motion (bar.x - 100) (top.toNat - 5))
  check "diagonal travel across another row retains toolbar owner" (diagonal.ui.hoverRow == some id && diagonal.ui.grace)
  let diagonal := hoverTime diagonal 1000
  check "travel grace is bounded to 400ms" ((hoverTime diagonal 1400).ui.grace == false)
  let barHover := pointerEvent hot (.motion (bar.x+20) (bar.y+12))
  check "crossing above a message into its toolbar retains ownership" (barHover.ui.hoverRow == some id && cursor barHover == 1)
  let timed := hoverTime barHover 1000
  check "tooltip stays hidden before its 400ms dwell" (!(hoverTime timed 1399).ui.tooltip)
  check "tooltip appears after its 400ms dwell" (hoverTime timed 1400).ui.tooltip
  check "moving within one action preserves dwell" (hoverTime (pointerEvent timed (.motion (bar.x+21) (bar.y+12))) 1400).ui.tooltip
  check "moving to another action restarts dwell" (!(pointerEvent (hoverTime timed 1400) (.motion (bar.x+110) (bar.y+12))).ui.tooltip)
  let reacted ← tap barHover (bar.x+20) (bar.y+12)
  check "hover toolbar opens the actual reaction component for its owner" (reacted.app.selected == some id && reacted.app.sheet.isSome)
  let more := pointerEvent barHover (.motion (bar.x+110) (bar.y+24))
  let opened ← tap more (bar.x+110) (bar.y+24)
  check "More opens for the hovered message" (opened.ui.moreFor == some id)
  let closed ← act opened .close
  check "Escape closes More before other navigation" (closed.ui.moreFor.isNone && closed.ui.context == .closed)
  let closed ← tap opened (bar.x+110) (bar.y+24)
  check "More toggles closed" closed.ui.moreFor.isNone
  let some menu := messageMenu d.layout d.height d.app id | throw (IO.userError "missing More geometry")
  let some row := opened.app.rows[id]? | throw (IO.userError "message gone")
  let empty := { opened with app := { opened.app with rows := opened.app.rows.insert id { row with data := { row.data with text := "" } } } }
  let empty := pointerEvent empty (.motion (menu.x+30) (menu.y+70))
  let stayed ← tap empty (menu.x+30) (menu.y+70)
  check "disabled Copy text stays inactive for image-only messages" (cursor empty == 0 && stayed.ui.moreFor == some id)
  let copied ← IO.mkRef ""
  let opened := { opened with app := { opened.app with io := { opened.app.io with copy := copied.set } } }
  let atCopy := pointerEvent opened (.motion (menu.x+30) (menu.y+70))
  discard <| tap atCopy (menu.x+30) (menu.y+70)
  check "hover menu copies the owned message through native clipboard API" ((← copied.get) == ((d.app.rows[id]?).map (·.data.text)).getD "")
  check "blur clears an open toolbar menu" ((pointerEvent opened .blur).ui.moreFor.isNone)
  let off := { hot with app := { hot.app with b := hot.app.b + 100000 } }
  check "unmounted/offscreen messages cannot retain a toolbar" ((messageBar off.layout off.height off.app id).isNone && (hoveredRow off.layout off.height off.ui off.app).isNone)
  for percent in [80, 100, 125, 200] do
    let resized ← zoom d percent
    let hot := pointerEvent resized (.motion (resized.app.dim.px 100) (resized.app.dim.px 28))
    check s!"pointer routes through current geometry at {percent}%" ((pointer hot.layout hot.height hot.ui (if hot.layout.nav.w > 0 then .nav else .main)).isSome)

end Desktop.HoverTest
