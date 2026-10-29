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

/-- Several real accepted communities, leaving the original selected. -/
def switcherCommunities : M Unit := do
  let current := (← get).cur
  for i in [0:16] do
    let name := if i == 0 then "Alexandria's community with a long name" else if i == 1 then "Zoë & Søren" else s!"Community {i + 1}"
    let w ← intentView (Community.found (Chaos.bytesOf s!"switcher identity {i}" 32)
      name.toUTF8 "Alice Nakamura".toUTF8 29330000
      (Chaos.bytesOf s!"switcher community {i}" 32) (Chaos.bytesOf s!"switcher key {i}" 32)
      (Chaos.bytesOf s!"switcher node {i}" 32))
    unless ← writeAll w do throw (IO.userError "switcher fixture rejected")
  refreshCommsNow
  switchToAcc current

def capture (dir name : String) (width height : Nat) (theme scenario : String) (zoom : Nat := 100) : IO Unit := do
  let hover := (scenario.splitOn "@").length > 1
  let fixtureName := (scenario.splitOn "@").head!
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
    if fixtureName == "conversation" then conversation
    if fixtureName == "sidebar" then sidebarPeople
    if fixtureName == "switcher-many" || fixtureName == "switcher-end" then switcherCommunities
    setTheme .system
    waitIdle sm).run d.app
  d := { d with app := s }
  let target : PageId := match fixtureName with
    | "home" => .home
    | "chat" | "conversation" | "sidebar" | "switcher" | "switcher-many" | "switcher-end" | "switcher-hover" => .chat
    | "you" => .you
    | "appearance" => .appearance
    | "community" => .communitySettings
    | "channel" => .channelSettings
    | "retention" | "disappearing" | "storage" | "leave" | "about" => .stub
    | "get-started" => .getStarted
    | "create" => .create
    | "paste" => .paste
    | _ => .home
  let title := match fixtureName with
    | "retention" => "Message retention" | "disappearing" => "Disappearing messages"
    | "storage" => "Storage on this device" | "leave" => "Leave community" | "about" => "About Quiet"
    | _ => ""
  if target == .stub || target == .appearance then
    let parent : PageId := if fixtureName == "about" || fixtureName == "appearance" then .you
      else if fixtureName == "disappearing" then .channelSettings else .communitySettings
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
  if fixtureName == "sidebar" then
    let names := d.app.members.toList.zip d.app.memberIds.toList
    IO.FS.writeFile (dir ++ "/sidebar-members.tsv") (String.intercalate "\n" (names.map fun ((name, _), id) =>
      s!"{name}\t{Pages.identity id}"))
  if fixtureName.startsWith "switcher" then
    d ← Desktop.act d .switcher
    if fixtureName == "switcher-end" then d ← Desktop.wheel d (d.app.dim.px 150) (d.app.dim.px 200) 100000
    if fixtureName == "switcher-hover" then
      d := { d with ui := { d.ui with hover := some (d.app.dim.px 275, d.app.dim.px 139) } }
    let m := Desktop.Switcher.model d.app d.height d.ui.switchOffset
    IO.FS.writeFile (dir ++ "/" ++ name ++ ".popup.tsv") s!"{m.box.x}\t{m.box.y}\t{m.box.w}\t{m.box.h}\t{m.offset}\t{m.contentH}\n"
    IO.FS.writeFile (dir ++ "/switcher-" ++ fixtureName ++ "-communities.tsv") (String.intercalate "\n" (d.app.comms.toList.map fun c => s!"{Pages.identity c.c}\t{c.name}"))
  if hover then
    let rest ← Desktop.picture d
    IO.FS.createDirAll (dir ++ "/rest")
    writePpm (dir ++ "/rest/" ++ name ++ ".ppm") rest.w rest.rows
    for line in (← IO.FS.readFile ("tests/visual/hover-reference/" ++ name ++ ".hover.tsv")).splitOn "\n" do
      if line.isEmpty then continue
      let parts := line.splitOn "\t"
      let some x := parts[0]?.bind String.toNat? | throw (IO.userError "invalid hover x")
      let some y := parts[1]?.bind String.toNat? | throw (IO.userError "invalid hover y")
      d := Desktop.pointerEvent d (.motion x y)
      d := Desktop.hoverTime (Desktop.hoverTime d 1000) 1401
  let bmp ← Desktop.picture d
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
