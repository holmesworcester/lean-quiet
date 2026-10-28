/-
Desktop integration without changing the phone app. The app still runs
App.step on its real database, writer and views. Its three layers feed
the desktop root; resize invalidates width-dependent row/page caches.
The platform supplies logical pixels and does only the final scale/blit.
-/
import platforms.desktop.View

namespace Desktop

structure Driver where
  app : App.St
  ui : Ui := {}
  width : Nat
  height : Nat
  layers : IO.Ref Layers
  screen : IO.Ref (Array UInt32)

def Driver.layout (d : Driver) : Layout := Desktop.layout d.width (d.ui.context != .closed)

def start (base : App.Io) (w h : Nat) (path : String)
    (net : Option (Nat × Bool) := none) : IO Driver := do
  let ls ← IO.mkRef ({} : Layers)
  let sc ← IO.mkRef #[w.toUInt32, (h - 40).toUInt32, 0, 0, 160]
  let io := { base with
    screen := sc.get
    frame := fun fr _ o top bot _ => do
      ls.set ⟨fr, top, bot, o.toNat⟩
      return #[] }
  let s ← App.start io (← sc.get) path net
  -- The offline build reduces the existing font to its original 16px
  -- cell. Font.row already handles that packing. Phones keep their font.
  let bytes ← IO.FS.readBinFile "out/desktop/font.bin"
  let font : Font.Font := ⟨bytes, 16, default⟩
  return ⟨{ s with font, dim := ⟨160, 16⟩ }, {}, w, h, ls, sc⟩

def resize (d : Driver) (w h : Nat) : IO Driver := do
  let d := { d with width := max 320 w, height := max 480 h }
  let g := d.layout
  let aw := max 275 g.main.w
  let ah := d.height - 40
  d.screen.set #[aw.toUInt32, ah.toUInt32, 0, 0, 160]
  let s := d.app
  let s := if s.W == aw && s.Hs == ah then s else
    { s with W := aw, Hs := ah, bgRow := Paint.solid Row.bg aw, rows := {}, heights := {}, imgs := {}, pageKey := none, chromeKey := "", gridKey := "", gridRows := {} }
  return { d with app := s }

def act (d : Driver) (a : Action) : IO Driver := do
  match a with
  | .settings => return { d with ui := { d.ui with context := .settings } }
  | .threads => return { d with ui := { d.ui with context := .threads } }
  | .close => return { d with ui := { d.ui with context := .closed } }
  | .previous => return { d with ui := { d.ui with first := d.ui.first - (d.height - 180) / 36 } }
  | .next =>
    let n := (d.height - 180) / 36
    return { d with ui := { d.ui with first := if d.ui.first + n < d.app.comms.size then d.ui.first + n else d.ui.first } }
  | .switcher =>
    if d.layout.nav.w > 0 then return { d with ui := { d.ui with switching := !d.ui.switching } }
    let (_, s) ← (App.openPage .switcher).run d.app
    return { d with app := s }
  | .community i =>
    d.app.io.textClear
    let (_, s) ← (do App.switchTo i; App.openPage .chat).run d.app
    return { d with app := { s with text := "", sel := #[0, 0, 0, 0] }, ui := { d.ui with switching := false } }
  | .send =>
    let (_, s) ← App.sendNow.run d.app
    return { d with app := s }
  | .photos =>
    let (_, s) ← App.attachPhoto.run d.app
    return { d with app := s }
  | .page p =>
    let (_, s) ← (App.openPage p).run d.app
    return { d with app := s, ui := { d.ui with context := .closed, switching := false } }

def tap (d : Driver) (x y : Nat) (long := false) : IO Driver := do
  let g := d.layout
  if let some c := hit (scene g d.height d.ui d.app) x y then return ← act d c.action
  if x < g.main.x || x ≥ g.main.x + g.main.w || y < 40 then return d
  let x := x - g.main.x
  let y := y - 40
  let s := d.app
  let bh := App.botH s
  let th := App.topH s
  let (r, py) := if y < th then (App.Region.header, y)
    else if y ≥ s.Hs - bh then (.composer, y - (s.Hs - bh))
    else (.list, (if s.page == .chat then s.b else 0) + s.Hs - bh - 1 - y)
  let (_, s) ← (App.onTap r x py long).run s
  return { d with app := s }

def tick (d : Driver) (events : List App.Event := []) : IO Driver := do
  let d ← resize d d.width d.height
  let (_, s) ← (App.step events).run d.app
  return { d with app := s }

def picture (d : Driver) : IO Paint.Bitmap := do
  return paint d.layout d.height d.ui d.app (← d.layers.get)

end Desktop
