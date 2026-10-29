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

def conversation : M Unit := do
  let s ← get
  let some key ← intentView (Community.currentKey s.me.c) | throw (IO.userError "visual key missing")
  let lines := #["Boathouse code changed this morning. It is 4417 now.",
    "Same one for the side gate.", "Ignore the laminated sign; nobody has replaced it.",
    "I will bring a spare key on Saturday.",
    "Forecast for Saturday is 14 knots gusting 22 from the south-west. I would rather take the pair out and do the long piece on Sunday when it drops to eight.",
    "Meet at the boathouse at seven.", "See you there!"]
  let mut root := none
  for i in [0:lines.size] do
    if i == 4 then root := none
    let op := sealedPost s.me.c s.me.adm s.me.dev key (Chaos.bytesOf s!"parity message {i}" 24)
      lines[i]!.toUTF8 (i + 1) (840 + i + (if i ≥ 4 then 6 else 0)) root
    unless ← write op do throw (IO.userError "visual message rejected")
    if root.isNone then root := some op.id

/-- Dense navigation is real signed membership/profile data, including long
names and non-Latin scripts. It exposes errors hidden by an empty sidebar. -/
def sidebarPeople : M Unit := do
  let s ← get
  for name in ["Bo Andersen", "Cassie Oyelaran", "Alexandria Montgomery-Worcester", "Γιώργος", "Анна", "Søren", "Zoë"] do
    let person := Device.named ("sidebar " ++ name)
    let bearer := Device.named ("sidebar invite " ++ name)
    let invitation := invite s.me.c s.me.adm s.me.dev bearer.pk false
    let req := request s.me.c invitation.id person (cryptoSeal.pub (Chaos.bytesOf ("sidebar node " ++ name) 32)) bearer.sk
    let approval := approve s.me.c req.id s.me.adm s.me.dev
    let admission := admit s.me.c req.id [approval.id]
    let profile := Community.profile s.me.c admission.id person name.toUTF8 29330000
    unless ← writeAll ⟨[invitation, req, approval, admission, profile]⟩ do
      throw (IO.userError "sidebar fixture rejected")

def capture (dir name : String) (width height : Nat) (theme page : String) : IO Unit := do
  let db := dir ++ "/" ++ name ++ ".db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (db ++ suffix) then IO.FS.removeFile (db ++ suffix)
  let sm ← Sim.new
  sm.viewport.set #[width.toUInt32, height.toUInt32, 0, 0, 160, if theme == "dark" then 1 else 0]
  let io := { sm.io with wall := pure (29330000, 0) }
  let mut d ← Desktop.start io width height db
  let (_, s) ← (do
    fixture
    if page == "conversation" then conversation
    if page == "sidebar" then sidebarPeople
    setTheme .system
    waitIdle sm).run d.app
  d := { d with app := s }
  let target : PageId := match page with
    | "home" => .home
    | "chat" | "conversation" | "sidebar" => .chat
    | "you" => .you
    | "appearance" => .appearance
    | "community" => .communitySettings
    | "channel" => .channelSettings
    | "retention" | "disappearing" | "storage" | "leave" | "about" => .stub
    | "get-started" => .getStarted
    | "create" => .create
    | "paste" => .paste
    | _ => .home
  let title := match page with
    | "retention" => "Message retention" | "disappearing" => "Disappearing messages"
    | "storage" => "Storage on this device" | "leave" => "Leave community" | "about" => "About Quiet"
    | _ => ""
  if target == .stub || target == .appearance then
    let parent : PageId := if page == "about" || page == "appearance" then .you
      else if page == "disappearing" then .channelSettings else .communitySettings
    d ← Desktop.act d (.page parent)
    let action : Pages.Act := if target == .appearance then .appearance else .stub title
    if width ≥ 720 then d ← Desktop.act d (.drawerAct action)
    else
      let (_, s) ← (App.onPageAct action).run d.app
      d := { d with app := s }
  else d ← Desktop.act d (.page target)
  for _ in [0:30] do
    d ← Desktop.tick d
    IO.sleep 2
  unless d.app.me.name == "Rowing club" &&
      (!(width ≥ 720 || target == .home || target == .you) || d.app.ownName == "Alice Nakamura") do
    throw (IO.userError s!"{name}: component query fixture did not settle: {d.app.ownName}, {d.app.people}")
  unless d.app.dim.theme == (if theme == "dark" then Theme.Value.dark else .light) do
    throw (IO.userError s!"{name}: wrong effective theme")
  IO.FS.writeFile (dir ++ "/identity.txt") s!"community={Pages.identity d.app.me.c}\nuser={Pages.identity d.app.me.user}\n"
  if page == "sidebar" then
    let names := d.app.members.toList.zip d.app.memberIds.toList
    IO.FS.writeFile (dir ++ "/sidebar-members.tsv") (String.intercalate "\n" (names.map fun ((name, _), id) =>
      s!"{name}\t{Pages.identity id}"))
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
