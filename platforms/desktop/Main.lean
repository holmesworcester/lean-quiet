/- Shared desktop application loop. Native shells supply only the OS seam. -/
import platforms.desktop.Input
import platforms.desktop.Presentation
import engine.renderer.Platform

namespace DesktopMain

private def platform : App.Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs,
   do return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, (← Platform.tzMin).toInt),
   Platform.scan, Platform.luma, Platform.log, (fun t => Platform.setText t), Platform.poll, Platform.links, Platform.motion, Platform.appearance, Platform.bars, (fun _ => pure false), pure (#[], .empty), ⟨Platform.editor, Platform.editorAction⟩,
   -- the desktop has no notifications or background service
   (fun _ => pure ()), (fun _ => pure false)⟩

/-- Shows a desktop frame; returns raw input records. Contract: its effect
is the OS's, which Lean does not state. -/
@[extern "lq_desktop_frame"] opaque desktopFrame (rows : @& Array ByteArray) (publication : UInt64) : IO (Array UInt32)
/-- Sets the mouse cursor's shape. Contract: its effect is the OS's, which
Lean does not state. -/
@[extern "lq_desktop_cursor"] opaque desktopCursor (kind : UInt32) : IO Unit
/-- Sets the native text selection. Contract: its effect is the OS's, which
Lean does not state. -/
@[extern "lq_desktop_select"] opaque desktopSelect (anchor caret : UInt32) : IO Unit

/-- Whether the desktop shell scrolls natively. Contract: none. The laws
hold for every value it returns. -/
@[extern "lq_desktop_native_scroll"] opaque desktopNativeScroll : IO Bool
/-- Publishes the desktop's list and hold layers with their placement.
Contract: its effect is the OS's, which Lean does not state. -/
@[extern "lq_desktop_layers"] opaque desktopLayers (list hold : @& Array ByteArray)
  (placement viewport : @& Array UInt32) : IO Unit

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
        controls := controls ++ s!"action {repr action} {d.layout.main.x + box.x + box.w/2} {App.topH d.app + box.y + box.h/2}\n"
        if let .theme choice := action then
          controls := controls ++ s!"choice {Theme.encode choice} {d.layout.main.x + box.x + box.w/2} {App.topH d.app + box.y + box.h/2}\n"
    for control in Desktop.scene d.layout d.height d.ui d.app do
      if let .popup (.community i) := control.action then
        controls := controls ++ s!"switch {i} {if (d.app.comms[i]?.map (·.acc == d.app.cur)).getD false then 1 else 0} {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
      if let .drawerAct (.theme choice) := control.action then
        controls := controls ++ s!"choice {Theme.encode choice} {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
      if control.action == .drawerAct .appearance then
        controls := controls ++ s!"appearance {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
      -- the sidebar's pages: general (chat) and Waiting to join (requests)
      if let .page p := control.action then
        controls := controls ++ s!"goto {repr p} {control.box.x + control.box.w/2} {control.box.y + control.box.h/2}\n"
    controls := controls ++ s!"field {d.app.field}\n"
    -- requests to join this community, and whether this device still waits
    controls := controls ++ s!"asking {d.app.asking.size} waiting {if d.app.me.waiting && !d.app.me.c.isEmpty then 1 else 0}\n"
    -- the newest mounted messages, newest first: the author's name (the
    -- community's member list's; a row under the same author's header
    -- draws none) and the text, quoted
    for (_, x) in d.app.ids.toList.take 12 do
      if let some r := d.app.rows[x]? then
        let name := ((d.app.memberIds.findIdx? (· == r.data.author)).bind (d.app.members[·]?)).map (·.1)
        let tallies := String.join (r.data.tallies.map fun t => s!" {t.emoji}{t.n}{if t.mine then "*" else ""}")
        controls := controls ++ s!"row {repr (name.getD r.data.name)} {repr r.data.text}{if r.data.pending then " pending" else ""}{tallies}\n"
    -- the hovered message's Add a reaction button, and the reaction
    -- sheet's quick keys while it is open
    if let some (id, _, _, _) := Desktop.hoveredRow d.layout d.height d.ui d.app then
      if let some bar := Desktop.messageBar d.layout d.height d.app id then
        controls := controls ++ s!"react {bar.x + d.app.dim.px 31} {bar.y + d.app.dim.px 24}\n"
    if let some sh := d.app.sheet then
      if !sh.catalog then
        let g := (Sheet.quick d.app.dim d.app.W).keys
        for i in [0:Row.quick.size] do
          controls := controls ++ s!"quick {Row.quick[i]!} {d.layout.main.x + g.left i + g.key / 2} {d.height - App.botH d.app + g.y0 + g.key / 2}\n"
    controls := controls ++ s!"pointer {repr d.ui.hover} cursor {Desktop.cursor d}\n"
    controls := controls ++ s!"tap {d.app.input.lastTap[0]?.getD 0} {d.app.input.lastTap[1]?.getD 0} {d.app.input.lastTap[2]?.getD 0}\n"
    controls := controls ++ s!"zoom {zoomPercent d} dpi {d.dpi} cell {d.app.font.cell}\n"
    controls := controls ++ s!"drawer {repr d.ui.drawer}\n"
    -- what a link did: the join it opened, or the toast that refused it
    if let some i := d.app.invite then controls := controls ++ s!"invite {i.text}\n"
    if let some (t, due) := d.app.toast then controls := controls ++ s!"toast {due} {t}\n"
    if let some bar := Desktop.scrollbar d.layout d.app then
      controls := controls ++ s!"scrollbar {bar.thumb.x} {bar.thumb.y} {bar.thumb.w} {bar.thumb.h} {bar.track.y} {bar.track.h} {bar.range}\n"
    IO.FS.writeFile (path ++ ".tmp") s!"{d.width} {d.height}\n{d.app.me.name}\n{repr d.ui.context}\n{repr d.app.page}\n{d.app.text}\n{d.app.total}\n{d.app.sel}\n{d.app.b}\n{controls}theme {Theme.encode d.app.theme.setting}\n"
    IO.FS.rename (path ++ ".tmp") path

partial def run (d : Desktop.Driver) (anchor : Option Nat := none) (scrollGrab : Option Nat := none) (native : Bool := false) : IO Desktop.Driver := do
  let mut d ← Desktop.tick d
  desktopCursor (Desktop.cursor d).toUInt32
  let layers ← d.layers.get
  let viewport := Desktop.scrollViewport d.layout d.height d.ui d.app layers
  if native then desktopLayers layers.list layers.hold layers.placement viewport
  traceState d
  let (published, ev) ← Desktop.publish d (fun publication pic => do
    return Desktop.Publication.decode (← desktopFrame pic.rows publication)) (native && viewport[0]! == 1)
  d := published
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
      d := Desktop.pointerEvent d (.motion x y)
      if z == 1 then
        if let some grab := scrollGrab then
          d := Desktop.cancelPresentation d
          d ← Desktop.scrollDrag d grab y
        if let some a := anchor then
          if let some c := Desktop.caret d x y then desktopSelect a.toUInt32 c.toUInt32
    else if k == 16 then
      d := Desktop.pointerEvent d (if z == 1 then .blur else .leave)
      if z == 1 then anchor := none; scrollGrab := none
    else if k == 10 then
      scrollGrab := Desktop.scrollGrab d x y
      anchor := if scrollGrab.isSome then none else Desktop.caret d x y
      if let some grab := scrollGrab then
        d := Desktop.cancelPresentation d
        d ← Desktop.scrollDrag d grab y
      if let some c := anchor then desktopSelect c.toUInt32 c.toUInt32
    else if k == 11 then anchor := none; scrollGrab := none
    else if k == 12 then d ← Desktop.act d .close
    else if k == 13 then d ← Desktop.resize d x y
    else if k == 19 then
      d := Desktop.cancelPresentation d
      d := { d with hoverStarted := 0, ui := { d.ui with hoverRow := none, moreFor := none, tooltip := false, grace := false } }
    else if k == 17 then
      d ← Desktop.resize { d with baseDpi := max 80 (min 1280 x), settled := (0, 0) } d.width d.height
    else if k == 14 then
      let step := d.app.dim.px 48
      d ← Desktop.wheel d x y (if z == 1 then -(Int.ofNat step) else Int.ofNat step)
    else if k == 15 then
      d ← Desktop.zoom d (zoomStep d x)
      anchor := none
      scrollGrab := none
      let db := (← IO.getEnv "QUIET_DB").getD "quiet-linux.db"
      IO.FS.writeFile (db ++ ".zoom") (toString (zoomPercent d))
  run d anchor scrollGrab native

/-- The argument after `flag`, if any (`--port 47101` gives "47101"). -/
def valueOf (args : List String) (flag : String) : Option String :=
  ((args.dropWhile (· != flag)).drop 1).head?

/-- The node, from the arguments: none (no sockets) with `--offline` or
`--demo`; else its port and whether its invites dial loopback. `--port N`
(1 to 65535; Link.port by default) lets two apps run on one machine, and
`--loopback` makes the links they issue dial 127.0.0.1, not this machine's
LAN addresses. -/
def netOf (args : List String) : Except String (Option (Nat × Bool)) :=
  let loop := args.contains "--loopback"
  if args.contains "--offline" || args.contains "--demo" then .ok none
  else if !args.contains "--port" then .ok (some (Link.port, loop))
  else match valueOf args "--port" >>= String.toNat? with
    | some n => if 0 < n && n < 65536 then .ok (some (n, loop)) else .error s!"--port {n}: a port is 1 to 65535"
    | none => .error s!"--port {(valueOf args "--port").getD ""}: a port is 1 to 65535"

#guard (netOf []).toOption == some (some (Link.port, false))
#guard (netOf ["--demo", "--port", "47101"]).toOption == some none
#guard (netOf ["--offline", "--loopback"]).toOption == some none
#guard (netOf ["--port", "47101", "--loopback"]).toOption == some (some (47101, true))
#guard (netOf ["--loopback", "--port", "65535"]).toOption == some (some (65535, true))
#guard (netOf ["--port", "0"]).toOption == none
#guard (netOf ["--port", "65536"]).toOption == none
#guard (netOf ["--port", "x"]).toOption == none
#guard (netOf ["--port"]).toOption == none

def main (args : List String) : IO Unit := do
  let net ← IO.ofExcept (netOf args)
  let sc ← Platform.screen
  let db := (← IO.getEnv "QUIET_DB").getD "quiet-linux.db"
  let mut d ← Desktop.start platform sc[0]!.toNat sc[1]!.toNat db net (sc[4]?.getD 160).toNat
  if ← System.FilePath.pathExists (db ++ ".zoom") then
    if let some percent := (← IO.FS.readFile (db ++ ".zoom")).trimAscii.toString.toNat? then
      d ← Desktop.zoom d percent
  if (args.contains "--demo" || args.contains "--seed") && d.app.comms.isEmpty then
    for name in ["Quiet", "Garden"] do
      let (_, s) ← (App.found name ((valueOf args "--name").getD "Alex")).run d.app
      d := { d with app := s }
      for _ in [0:50] do d ← Desktop.tick d; IO.sleep 2
    d ← Desktop.act d (.community (d.app.comms.findIdx? (·.name == "Quiet") |>.getD 0))
    for message in ["Welcome to Lean Quiet.", "Noto: café · Ελληνικά · שלום · 日本語 · 🙂"] do
      let (_, s) ← (App.sendText message).run d.app
      d := { d with app := s }
  if let some n := ((args.dropWhile (· != "--chaos")).drop 1).head? >>= String.toNat? then
    if d.app.comms.isEmpty then throw (IO.userError "Create a community before generating chaos")
    let (_, s) ← (App.command s!"chaos {min n 5000}").run d.app
    d := { d with app := s }
  if args.contains "--scroll-fixture" then
    for i in [0:40] do
      let (_, s) ← (App.sendText s!"Scroll history {i}: older messages remain reachable.").run d.app
      d := { d with app := s }
  -- Add members, opened as its button opens it: it issues the current
  -- community's link (once a session), which goes to the file as well
  if let some file := valueOf args "--invite" then
    d ← Desktop.act d (.drawerAct .addMembers)
    -- the link is issued by a reader act: the app's frames complete it
    for _ in [0:5000] do
      if d.app.links.any (·.1 == d.app.me.acc) then break
      d ← Desktop.tick d; IO.sleep 2
    match d.app.links.find? (·.1 == d.app.me.acc) with
    | some (_, link) =>
      IO.FS.writeFile (file ++ ".tmp") (link ++ "\n")
      IO.FS.rename (file ++ ".tmp") file
    | none =>
      -- exit, not throw: the writer's dedicated task never ends on its own
      IO.eprintln "--invite: no link was issued (found or join a community first)"
      IO.Process.exit 1
  d ← run d none none (← desktopNativeScroll)
  if let some r := d.app.net then r.stop
  -- The existing writer is a dedicated infinite task. Drain accepted
  -- writes before exiting; returning alone waits forever for that task.
  while (← d.app.wr.busy.get) > 0 do IO.sleep 2
  IO.Process.exit 0

end DesktopMain
