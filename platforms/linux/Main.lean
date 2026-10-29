/- The Linux executable. All drawing/layout remains in Quiet.Desktop. -/
import platforms.desktop.Input
import engine.renderer.Platform

private def platform : App.Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs,
   do return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, (← Platform.tzMin).toInt),
   Platform.scan, Platform.luma, Platform.log, (fun t => Platform.setText t), Platform.poll, Platform.links, Platform.motion, Platform.appearance, Platform.bars, (fun _ => pure false), pure (#[], .empty)⟩

@[extern "lq_desktop_frame"] opaque desktopFrame (rows : @& Array ByteArray) : IO (Array UInt32)
@[extern "lq_desktop_select"] opaque desktopSelect (anchor caret : UInt32) : IO Unit

private def zoomLevels : List Nat := [50, 67, 75, 80, 90, 100, 110, 125, 150, 175, 200]

private def zoomPercent (d : Desktop.Driver) : Nat := d.requestedZoom

private def zoomStep (d : Desktop.Driver) (direction : Nat) : Nat :=
  let current := zoomPercent d
  if direction == 0 then 100
  else if direction == 1 then (zoomLevels.find? (· > current)).getD 200
  else ((zoomLevels.filter (· < current)).getLast?).getD 50

private def traceState (d : Desktop.Driver) : IO Unit := do
  if let some path ← IO.getEnv "QUIET_STATE" then
    -- written whole, then renamed: a reader never sees it half written
    let c := App.composerLayout d.app
    let x := d.layout.main.x + c.textX
    let y := d.height - App.botH d.app + c.textY
    let mut controls := s!"editor {x} {y} {x + (App.cursorAt d.app 5).2}\n"
    if let some pg := d.app.pageNow then
      for (box, action) in pg.taps do
        if let .theme choice := action then
          controls := controls ++ s!"choice {Theme.encode choice} {d.layout.main.x + box.x + box.w/2} {App.topH d.app + box.y + box.h/2}\n"
    for control in Desktop.scene d.layout d.height d.ui d.app do
      if let .popup (.community i) := control.action then
        controls := controls ++ s!"switch {i} {if (d.app.comms[i]?.map (·.acc == d.app.cur)).getD false then 1 else 0} {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
      if let .drawerAct (.theme choice) := control.action then
        controls := controls ++ s!"choice {Theme.encode choice} {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
      if control.action == .drawerAct .appearance then
        controls := controls ++ s!"appearance {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
    controls := controls ++ s!"zoom {zoomPercent d} dpi {d.dpi} cell {d.app.font.cell}\n"
    controls := controls ++ s!"drawer {repr d.ui.drawer}\n"
    if let some bar := Desktop.scrollbar d.layout d.app then
      controls := controls ++ s!"scrollbar {bar.thumb.x} {bar.thumb.y} {bar.thumb.w} {bar.thumb.h} {bar.track.y} {bar.track.h} {bar.range}\n"
    IO.FS.writeFile (path ++ ".tmp") s!"{d.width} {d.height}\n{d.app.me.name}\n{repr d.ui.context}\n{repr d.app.page}\n{d.app.text}\n{d.app.total}\n{d.app.sel}\n{d.app.b}\n{controls}theme {Theme.encode d.app.theme.setting}\n"
    IO.FS.rename (path ++ ".tmp") path

partial def run (d : Desktop.Driver) (anchor : Option Nat := none) (scrollGrab : Option Nat := none) : IO Desktop.Driver := do
  let mut d ← Desktop.tick d
  let pic ← Desktop.picture d
  traceState d
  let ev ← desktopFrame pic.rows
  let mut anchor := anchor
  let mut scrollGrab := scrollGrab
  for i in [0:ev.size / 4] do
    let k := ev[4*i]!
    let x := ev[4*i+1]!.toNat
    let y := ev[4*i+2]!.toNat
    let z := ev[4*i+3]!.toNat
    if k == 1 then return d
    else if k == 2 || k == 3 then
      if scrollGrab.isNone then d ← Desktop.tap d x y (k == 3)
    else if (k == 4 || k == 5) && !d.ui.switching then
      let (_, s) ← (App.onEvent (if k == 4 then .text else .send)).run d.app
      d := { d with app := s }
    else if k == 9 then
      d := { d with ui := { d.ui with hover := (x, y) } }
      if z == 1 then
        if let some grab := scrollGrab then Desktop.scrollDrag d grab y
        if let some a := anchor then
          if let some c := Desktop.caret d x y then desktopSelect a.toUInt32 c.toUInt32
    else if k == 10 then
      scrollGrab := Desktop.scrollGrab d x y
      anchor := if scrollGrab.isSome then none else Desktop.caret d x y
      if let some grab := scrollGrab then Desktop.scrollDrag d grab y
      if let some c := anchor then desktopSelect c.toUInt32 c.toUInt32
    else if k == 11 then anchor := none; scrollGrab := none
    else if k == 12 then d ← Desktop.act d .close
    else if k == 13 then d ← Desktop.resize d x y
    else if k == 14 then
      let step := d.app.dim.px 48
      d ← Desktop.wheel d x y (if z == 1 then -(Int.ofNat step) else Int.ofNat step)
    else if k == 15 then
      d ← Desktop.zoom d (zoomStep d x)
      anchor := none
      scrollGrab := none
      let db := (← IO.getEnv "QUIET_DB").getD "quiet-linux.db"
      IO.FS.writeFile (db ++ ".zoom") (toString (zoomPercent d))
  run d anchor scrollGrab

def main (args : List String) : IO Unit := do
  let sc ← Platform.screen
  let db := (← IO.getEnv "QUIET_DB").getD "quiet-linux.db"
  let net := if args.contains "--offline" || args.contains "--demo" then none else some (Link.port, false)
  let mut d ← Desktop.start platform sc[0]!.toNat sc[1]!.toNat db net
  if ← System.FilePath.pathExists (db ++ ".zoom") then
    if let some percent := (← IO.FS.readFile (db ++ ".zoom")).trimAscii.toString.toNat? then
      d ← Desktop.zoom d percent
  if args.contains "--demo" && d.app.comms.isEmpty then
    for name in ["Quiet", "Garden"] do
      let (_, s) ← (App.found name "Alex").run d.app
      d := { d with app := s }
      for _ in [0:50] do d ← Desktop.tick d; IO.sleep 2
    d ← Desktop.act d (.community (d.app.comms.findIdx? (·.name == "Quiet") |>.getD 0))
    for message in ["Welcome to Lean Quiet.", "Noto: café · Ελληνικά · שלום · 日本語 · 🙂"] do
      let (_, s) ← (App.sendText message).run d.app
      d := { d with app := s }
  if args.contains "--scroll-fixture" then
    for i in [0:40] do
      let (_, s) ← (App.sendText s!"Scroll history {i}: older messages remain reachable.").run d.app
      d := { d with app := s }
  d ← run d
  if let some r := d.app.net then r.stop
  -- The existing writer is a dedicated infinite task. Drain accepted
  -- writes before exiting; returning alone waits forever for that task.
  while (← d.app.wr.busy.get) > 0 do IO.sleep 2
  IO.Process.exit 0
