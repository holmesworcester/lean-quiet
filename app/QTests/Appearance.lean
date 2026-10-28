/-
Appearance on the running headless app. Real SQLite restarts are separate
processes. Live OS changes go through Io.screen and App.step. Raster
checks compare warm paints with fresh paints, including scrims and all
page kinds at Pixel 7 and iPhone 16e sizes.
-/
import Quiet
import QTests.Sim

open App Paint

def demand (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError s!"FAIL {name}")
  IO.println s!"ok {name}"

def cleanDb (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)

def tapChoice (setting : Theme.Setting) : M Unit := do
  let s ← get
  let some pg := s.pageNow | throw (IO.userError "no appearance page")
  let some (box, _) := pg.taps.find? (·.2 == .theme setting) | throw (IO.userError "no choice")
  onTap .list (box.x + box.w/2) (viewH s - 1 - (box.y + box.h/2)) false

/-- Audit every foreground pixel recorded by the glyph painter. -/
def glyphsPass (b : Bitmap) : Bool := b.strokes.all fun s => Id.run do
  let mut ok := true
  for i in [0:s.n] do
    if s.bits &&& (0x8000000000000000 >>> i.toUInt64) != 0 && s.x+i < b.w && s.y < b.h then
      let drawn := getPx b.rows[s.y]! (s.x+i)
      ok := ok && drawn == textColor s.ink s.ground i &&
        decide (Contrast.meets drawn (getPx s.ground i))
  return ok

def pages : Array (PageId × String) := #[
  (.getStarted, "start"), (.create, "create"), (.createName, "create-name"),
  (.joinChoice, "join"), (.openInvite, "invite-choice"), (.paste, "paste"),
  (.scan, "scan"), (.name, "name"), (.agree, "agree"), (.waiting, "waiting"),
  (.requests, "requests"), (.invite, "invite"), (.switcher, "switcher"),
  (.home, "home"), (.profile, "profile"), (.removeConfirm, "remove"),
  (.you, "you"), (.appearance, "appearance")]

def exercise (dir : String) (screen : Array UInt32) : IO Unit := do
  cleanDb dir
  let sm ← Sim.new
  let os ← IO.mkRef (0 : UInt32)
  let bars ← IO.mkRef (false, (0 : UInt32))
  let base := sm.io
  let io := { base with
    screen := do return screen.push (← os.get)
    appearance := fun dark fill => bars.set (dark, fill) }
  let s ← App.start io (screen.push 0) (dir ++ "/quiet.db")
  let testGlyph := (Bitmap.blank 160 80 (solid (Palette.color .light .bg) 160)).glyph
    s.font 65 8 8 (Palette.color .light .bg) false
  demand "real glyph corrects an invisible requested ink" (!testGlyph.strokes.isEmpty && glyphsPass testGlyph)

  demand "default follows system light" (s.theme.setting == .system && s.dim.theme == .light)
  let (_, s) ← (do
    found "Theme room" "Alice"
    waitIdle sm
    onPageAct (.openChannel 0)
    let _ ← sendText "A real message: light and dark, مرحبا 世界."
    waitIdle sm
    openPage .you
    steps 2
    onPageAct .appearance
    steps 2
    tapChoice .dark
    steps 2).run s
  demand "Appearance tap stores Dark" (s.theme.setting == .dark && (← Theme.load s.rd) == .dark)
  demand "bar icons follow forced Dark" (← bars.get).1
  os.set 1
  let (_, s) ← (steps 2).run s
  demand "forced choice survives OS change" (s.dim.theme == .dark)
  let (_, s) ← (tapChoice .system *> steps 2).run s
  demand "System uses latest OS value" (s.theme.setting == .system && s.dim.theme == .dark)
  let (_, s) ← (onPageAct (.openChannel 0) *> waitIdle sm).run s
  demand "real message has cached paints" (!s.rows.isEmpty && s.rows.toList.any (·.2.shown.isSome))
  let old ← sm.last.get
  os.set 0
  let (_, s) ← (waitIdle sm).run s
  demand "live OS switch repaints all layers" (s.dim.theme == .light && (← sm.last.get) != old)
  demand "live bar icons follow Light" (!(← bars.get).1)
  demand "header and composer equal fresh paints" (s.topBmp.rows == (header s).rows && s.botBmp.rows == (composer s).rows)
  for (_, r) in s.rows.toList do
    if let some b := r.shown then
      let expected := Row.paint s.font s.dim s.W s.bgRow r.data r.lay none #[]
      demand "warm row equals fresh light paint" (b.rows == expected.rows)
      demand "row glyph contrast" (glyphsPass b && !b.strokes.isEmpty)
      let shaded := Scrim.shade b
      demand "scrim preserves visible text contrast" (glyphsPass shaded && !shaded.strokes.isEmpty)
  os.set 1
  let (_, s) ← (do
    let _ ← command "tray 0"
    let _ ← command "browse"
    waitIdle sm).run s
  demand "selected message paints its shape cue" (s.rows.toList.any fun (_, r) => r.data.selected && r.shown.isSome)
  demand "catalogue has cached cells" (!s.gridRows.isEmpty)
  os.set 0
  let (_, s) ← (waitIdle sm).run s
  let some sh := s.sheet | throw (IO.userError "no sheet")
  for (index, bmp) in s.gridRows.toList do
    let expected := Sheet.gridRow s.font s.dim s.W (catOf s sh) s.catalog (sheetItems s sh)
      sh.tone (mineOn s (s.selected.getD .empty)) index
    demand "cached sheet cell equals fresh light paint" (bmp.rows == expected.rows)
  for theme in [Theme.Value.light, .dark] do
    let t : Theme.State := ⟨if theme == .light then .light else .dark, theme⟩
    let fresh := themed s t
    for (page, name) in pages do
      let key := pageIn { fresh with page, field := "Quiet", refusal := some "Invalid invite", profileOf := some (fresh.me.user, "Alice", true) }
      let (pg, top) := drawPage fresh.font fresh.bgRow none key
      demand s!"{repr theme}/{name} glyph contrast" (glyphsPass pg.bmp && glyphsPass top)
      writePpm s!"{dir}/{repr theme}-{name}.ppm" s.W (top.rows ++ pg.bmp.rows ++ Array.replicate (fresh.insetBot + 1) fresh.bgRow)
    let some (_, row) := s.rows.toList.head? | throw (IO.userError "no row")
    let selected := Row.paint s.font fresh.dim s.W fresh.bgRow { row.data with selected := true } row.lay none #[]
    demand s!"{repr theme} selected row has shape cue" (selected.strokes.size > (Row.paint s.font fresh.dim s.W fresh.bgRow { row.data with selected := false } row.lay none #[]).strokes.size)
    let b := Pages.toast s.font fresh.dim s.W "Saved"
    demand s!"{repr theme} toast contrast" (glyphsPass b)
    for under in [0x000000, 0xffffff, 0x888888, 0x7647c7, 0xc7353b] do
      let source := solid (Palette.color theme .toast) 40
      let painted := Overlay.toastRow theme (solid under 80) source 10 0 40 30 0 2
      demand s!"{repr theme} actual composited edge {under}"
        (decide (Contrast.meets (getPx painted 25) under 30))

      demand s!"{repr theme} composited edge {under}" (decide (Contrast.meets (Overlay.edge theme under) under 30))
  IO.println "appearance raster suite complete"

def run (args : List String) : IO UInt32 := do
  let mode := args[0]?.getD "live"
  let dir := args[1]?.getD "out/appearance"
  if mode == "palette" then
    let tokens : Array (Palette.Token × String) := #[
      (.bg, "bg"), (.panel, "panel"), (.line, "line"), (.fg, "fg"), (.muted, "muted"),
      (.accent, "accent"), (.button, "button-bg"), (.onAccent, "on-accent"),
      (.accentInk, "accent-ink"), (.link, "link"), (.tint, "tint"), (.warning, "warning"),
      (.error, "error"), (.danger, "danger"), (.online, "online"), (.selected, "selected"),
      (.scrim, "scrim"), (.toast, "toast"), (.toastInk, "toast-ink"), (.edge, "edge"),
      (.badge, "badge"), (.badgeInk, "badge-ink"), (.avatar, "avatar"), (.black, "black"), (.white, "white")]
    IO.FS.createDirAll dir
    let mut rows := #[]
    for theme in [Theme.Value.light, .dark] do
      let mut row := ByteArray.empty
      for (token, name) in tokens do
        let color := Palette.color theme token
        IO.println s!"{if theme == .light then "light" else "dark"} {name} {color.toNat}"
        row := row ++ solid color 1
      for i in [0:8] do
        let color := Palette.avatar (toString i)
        IO.println s!"{if theme == .light then "light" else "dark"} avatar{i} {color.toNat}"
        row := row ++ solid color 1
      rows := rows.push row
    writePpm (dir ++ "/palette.ppm") (tokens.size + 8) rows
  else if mode == "write" || mode == "read" then
    IO.FS.createDirAll dir
    let setting := Theme.decode (args[2]?.getD "system")
    let sm ← Sim.new
    let s ← App.start sm.io #[1080, 2400, 128, 63, 420, 1] (dir ++ "/quiet.db")
    if mode == "write" then
      let _ ← (setTheme setting).run s
      demand "persisted device setting" ((← Theme.load s.rd) == setting)
    else
      demand "fresh process restores setting" (s.theme.setting == setting)
      demand "fresh process resolves new OS value" (s.dim.theme == Theme.effective ⟨setting, .dark⟩)
  else
    exercise (dir ++ "/pixel7") #[1080, 2400, 128, 63, 420]
    exercise (dir ++ "/iphone16e") #[1170, 2532, 141, 102, 480]
  IO.Process.exit 0

def main (args : List String) : IO UInt32 := do
  match ← (run args).toBaseIO with
  | .ok code => IO.Process.exit code.toUInt8
  | .error err =>
    IO.eprintln (toString err)
    IO.Process.exit 1
