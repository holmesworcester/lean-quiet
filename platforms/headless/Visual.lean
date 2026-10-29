/- Pixel comparison fixtures use the real database, component queries and
desktop/mobile renderer. Only the clock, identity and input are fixtures. -/
import platforms.headless.Sim
import platforms.desktop.Driver

open App Engine Community Data

namespace Visual

def fixture : M Unit := do
  let w ← intentView (Community.found (Chaos.bytesOf "parity identity" 32)
    "Rowing club".toUTF8 "Alice Nakamura".toUTF8 29330000
    (Chaos.bytesOf "parity community" 32) (Chaos.bytesOf "parity key" 32)
    (Chaos.bytesOf "parity node" 32))
  unless ← writeAll w do throw (IO.userError "visual fixture rejected")
  let some a := acceptOf w | throw (IO.userError "fixture acceptance missing")
  refreshCommsNow
  switchToAcc a

def capture (dir name : String) (width height : Nat) (theme page : String) (zoom : Nat := 100) : IO Unit := do
  let db := dir ++ "/" ++ name ++ ".db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (db ++ suffix) then IO.FS.removeFile (db ++ suffix)
  let sm ← Sim.new
  sm.viewport.set #[width.toUInt32, height.toUInt32, 0, 0, 160, if theme == "dark" then 1 else 0]
  let io := { sm.io with wall := pure (29330000, 0) }
  let mut d ← Desktop.start io width height db
  d ← Desktop.zoom d zoom
  let (_, s) ← (do
    fixture
    setTheme .system
    waitIdle sm).run d.app
  d := { d with app := s }
  let target : PageId := match page with
    | "home" => .home
    | "chat" => .chat
    | "you" => .you
    | "appearance" => .appearance
    | "community" => .communitySettings
    | "channel" => .channelSettings
    | "get-started" => .getStarted
    | "create" => .create
    | "paste" => .paste
    | _ => .home
  d ← Desktop.act d (.page target)
  for _ in [0:30] do
    d ← Desktop.tick d
    IO.sleep 2
  unless d.app.me.name == "Rowing club" &&
      (!(width ≥ 720 || target == .home || target == .you) || d.app.ownName == "Alice Nakamura") do
    throw (IO.userError s!"{name}: component query fixture did not settle: {d.app.ownName}, {d.app.people}")
  unless d.app.dim.theme == (if theme == "dark" then Theme.Value.dark else .light) do
    throw (IO.userError s!"{name}: wrong effective theme")
  IO.FS.writeFile (dir ++ "/identity.txt") s!"community={Pages.identity d.app.me.c}\nuser={Pages.identity d.app.me.user}\n"
  let bmp := Desktop.paint d.layout d.height d.ui d.app (← d.layers.get)
  if bmp.w != width || bmp.h != height then
    throw (IO.userError s!"{name}: wrong dimensions {bmp.w}x{bmp.h}")
  writePpm (dir ++ "/" ++ name ++ ".ppm") bmp.w bmp.rows
  IO.FS.writeFile (dir ++ "/" ++ name ++ ".geometry.txt")
    s!"width={width} height={height} nav={d.layout.nav.x},{d.layout.nav.w} main={d.layout.main.x},{d.layout.main.w} context={d.layout.context.x},{d.layout.context.w}\n"
  d.app.raster.reconcile []
  IO.println s!"visual: {name}"

def run (args : List String) : IO Unit := do
  let dir := args[0]?.getD "out/visual/actual"
  let manifest := args[1]?.getD "tests/visual/cases.tsv"
  IO.FS.createDirAll dir
  for line in (← IO.FS.readFile manifest).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [name, w, h, theme, page, zoom] =>
      let some w := w.toNat? | throw (IO.userError "invalid visual width")
      let some h := h.toNat? | throw (IO.userError "invalid visual height")
      let some zoom := zoom.toNat? | throw (IO.userError "invalid visual zoom")
      capture dir name w h theme page zoom
    | [name, w, h, theme, page] =>
      let some w := w.toNat? | throw (IO.userError "invalid visual width")
      let some h := h.toNat? | throw (IO.userError "invalid visual height")
      capture dir name w h theme page
    | _ => throw (IO.userError s!"invalid visual case: {line}")

end Visual

def main (args : List String) : IO Unit := do
  try
    Visual.run args
    (← IO.getStdout).flush
    IO.Process.exit 0
  catch e =>
    IO.eprintln s!"visual: {e}"
    IO.Process.exit 1
