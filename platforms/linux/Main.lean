/- The Linux executable. All drawing/layout remains in Quiet.Desktop. -/
import platforms.desktop.Input
import engine.renderer.Platform

private def platform : App.Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, Platform.textClear, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s,
   Platform.nowUs,
   do return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, (← Platform.tzMin).toInt),
   Platform.scan, Platform.luma, Platform.log⟩

@[extern "lq_desktop_frame"] opaque desktopFrame (rows : @& Array ByteArray) : IO (Array UInt32)
@[extern "lq_desktop_select"] opaque desktopSelect (anchor caret : UInt32) : IO Unit

private def traceState (d : Desktop.Driver) : IO Unit := do
  if let some path ← IO.getEnv "QUIET_STATE" then
    -- written whole, then renamed: a reader never sees it half written
    IO.FS.writeFile (path ++ ".tmp") s!"{d.width} {d.height}\n{d.app.me.name}\n{repr d.ui.context}\n{repr d.app.page}\n{d.app.text}\n{d.app.total}\n{d.app.sel}\n{d.app.b}\n"
    IO.FS.rename (path ++ ".tmp") path

partial def run (d : Desktop.Driver) (anchor : Option Nat := none) : IO Desktop.Driver := do
  let mut d ← Desktop.tick d
  let pic ← Desktop.picture d
  traceState d
  let ev ← desktopFrame pic.rows
  let mut anchor := anchor
  for i in [0:ev.size / 4] do
    let k := ev[4*i]!
    let x := ev[4*i+1]!.toNat
    let y := ev[4*i+2]!.toNat
    let z := ev[4*i+3]!.toNat
    if k == 1 then return d
    else if k == 2 || k == 3 then d ← Desktop.tap d x y (k == 3)
    else if k == 4 || k == 5 then
      let (_, s) ← (App.onEvent (if k == 4 then .text else .send)).run d.app
      d := { d with app := s }
    else if k == 9 then
      d := { d with ui := { d.ui with hover := (x, y) } }
      if z == 1 then
        if let some a := anchor then
          if let some c := Desktop.caret d x y then desktopSelect a.toUInt32 c.toUInt32
    else if k == 10 then
      anchor := Desktop.caret d x y
      if let some c := anchor then desktopSelect c.toUInt32 c.toUInt32
    else if k == 11 then anchor := none
    else if k == 12 then d ← Desktop.act d .close
    else if k == 13 then d ← Desktop.resize d x y
    else if k == 14 then
      let g := d.layout
      if x ≥ g.main.x && x < g.main.x + g.main.w && y ≥ 40 && d.app.page == .chat then
        Platform.scrollBy (if z == 1 then 48 else -48)
  run d anchor

def main (args : List String) : IO Unit := do
  let sc ← Platform.screen
  let db := (← IO.getEnv "QUIET_DB").getD "quiet-linux.db"
  let net := if args.contains "--offline" || args.contains "--demo" then none else some (Link.port, false)
  let mut d ← Desktop.start platform sc[0]!.toNat sc[1]!.toNat db net
  if args.contains "--demo" && d.app.comms.isEmpty then
    for name in ["Quiet", "Garden"] do
      let (_, s) ← (App.found name "Alex").run d.app
      d := { d with app := s }
      for _ in [0:50] do d ← Desktop.tick d; IO.sleep 2
    d ← Desktop.act d (.community 0)
    let (_, s) ← (App.sendText "Welcome to Lean Quiet on Linux.").run d.app
    d := { d with app := s }
  d ← run d
  if let some r := d.app.net then r.stop
  -- The existing writer is a dedicated infinite task. Drain accepted
  -- writes before exiting; returning alone waits forever for that task.
  while (← d.app.wr.busy.get) > 0 do IO.sleep 2
  IO.Process.exit 0
