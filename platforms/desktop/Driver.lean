/-
Desktop integration without changing the phone app. The app still runs
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
  layers : IO.Ref Layers
  screen : IO.Ref (Array UInt32)
  /-- The app's size (W, Hs) in the frame last settled. -/
  settled : Nat × Nat := (0, 0)

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
  -- Use the app's density-scaled font, including Noto and colour emoji.
  -- Replacing it with the old reduced bitmap discards the shared renderer.
  return { app := s, width := w, height := h, layers := ls, screen := sc }

def resize (d : Driver) (w h : Nat) : IO Driver := do
  let d := { d with width := max 320 w, height := max 480 h }
  let g := d.layout
  let aw := max 275 g.main.w
  let ah := d.height - 40
  d.screen.set #[aw.toUInt32, ah.toUInt32, 0, 0, 160]
  let (_, s) ← (App.resize (← d.screen.get)).run d.app
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
    decoded ← d.app.imgs.toList.allM fun (_, t) => IO.hasFinished t
    let (_, s) ← (App.step []).run d.app
    d := { d with app := s }
  return { d with settled := (d.app.W, d.app.Hs) }

def tick (d : Driver) (events : List App.Event := []) : IO Driver := do
  let d ← resize d d.width d.height
  let (_, s) ← (App.step events).run d.app
  let d := { d with app := s }
  if (s.W, s.Hs) != d.settled then settleFrame d else return d

def picture (d : Driver) : IO Paint.Bitmap := do
  return paint d.layout d.height d.ui d.app (← d.layers.get)

end Desktop
