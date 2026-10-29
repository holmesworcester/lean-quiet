/-
The desktop root: the existing app's pixels in a fluid middle track,
community navigation on the left, and a settings/threads context on the
right. Controls are painted and dispatched from Layout.controls. The
threads surface reports the missing reply domain honestly.
-/
import App
import engine.renderer.TranslatePaint
import engine.renderer.desktop.Layout
import engine.renderer.desktop.Scrollbar

namespace Desktop
open Paint

inductive Context where
  | closed | settings | threads
  deriving BEq, Repr, Inhabited

inductive Action where
  | switcher | community (i : Nat) | settings | threads | close
  | page (p : App.PageId) | previous | next
  | send | photos
  deriving BEq, Repr, Inhabited

structure Ui where
  context : Context := .closed
  switching : Bool := false
  first : Nat := 0
  hover : Nat × Nat := (0, 0)
  deriving Inhabited

structure Layers where
  list : Array ByteArray := #[]
  top : Array ByteArray := #[]
  bot : Array ByteArray := #[]
  over : Nat := 0
  placement : Array UInt32 := #[]
  hold : Array ByteArray := #[]
  deriving Inhabited

def purple : Color := 0x7647C7
def hoverColor : Color := 0x916AD2

def label (f : Font.Font) (b : Bitmap) (s : String) (x y w : Nat)
    (color : Color := Row.nameInk) : Bitmap :=
  b.line f (Text.oneLine f w s) x y color

def candidates (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) := Id.run do
  let mut out := []
  let add (p : Pane) (x y w h : Nat) (a : Action) (t : String) : Control Action :=
    ⟨p, ⟨x, y, w, h⟩, a, t⟩
  if g.nav.w > 0 then
    out := out ++ [add .nav 16 12 188 32 .switcher (if ui.switching then "Communities  v" else s.me.name ++ "  v")]
    if ui.switching then
      let slots := (h - 180) / 36
      for i in [ui.first:min s.comms.size (ui.first + slots)] do
        out := out ++ [add .nav 8 (68 + (i - ui.first) * 36) 204 32 (.community i)
          ((if s.comms[i]!.acc == s.cur then "* " else "  ") ++ s.comms[i]!.name)]
      out := out ++ [add .nav 8 (h - 100) 96 32 .previous "Previous",
        add .nav 112 (h - 100) 100 32 .next "Next",
        add .nav 8 (h - 60) 204 32 (.page .getStarted) "+ Add community"]
    else
      out := out ++ [add .nav 8 76 204 26 (.page .invite) "+ Add members",
        add .nav 8 102 204 26 .threads "  Threads",
        add .nav 8 184 204 26 (.page .chat) "# general",
        add .nav 8 246 204 30 (.page .home) "  People",
        add .nav 8 (h - 48) 204 36 .settings "  Settings"]
  if g.context.w > 0 then
    let x := g.context.x
    out := out ++ [add .context (x + g.context.w - 40) 8 32 32 .close "x"]
    if ui.context == .settings then
      out := out ++ [add .context (x + 16) 80 (g.context.w - 32) 48 (.page .invite) "Add members",
        add .context (x + 16) 136 (g.context.w - 32) 48 (.page .requests) "Join requests",
        add .context (x + 16) 192 (g.context.w - 32) 48 (.page .home) "People",
        add .context (x + 16) 248 (g.context.w - 32) 48 (.page .switcher) "Communities",
        add .context (x + 16) 304 (g.context.w - 32) 48 (.page .appearance) "Appearance"]
  return out

def scene (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) :=
  controls g h (candidates g h ui s)

/-- Compose the app's actual three layers, in their own track. -/
def content (w h : Nat) (ls : Layers) (background : Color := Row.bg) : Bitmap :=
  ⟨w, Translate.compose ls.placement (ls.placement[15]?.getD 0).toInt32 h
    (solid background w) ls.list ls.top ls.bot ls.hold, #[]⟩

def scrollbar (g : Layout) (s : App.St) : Option Scrollbar.Bar :=
  if g.main.w == 0 || s.page != .chat || s.sheet.isSome then none else
  Scrollbar.layout (g.main.x + g.main.w) (App.geom s).top (App.geom s).viewNow (App.bottoms s).2 s.b

/-- Painting traverses exactly `scene`, the list hit testing consumes. -/
def paint (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (ls : Layers) : Bitmap := Id.run do
  let color := Palette.color s.dim.theme
  let nav := color .accent
  let mut b := Bitmap.blank g.width h (solid (color .bg) g.width)
  if g.main.w > 0 then
    b := b.image (content g.main.w h ls (color .bg)) g.main.x 0 0
  if g.nav.w > 0 then
    b := b.fill 0 0 g.nav.w h nav
    if !ui.switching then
      b := label s.font b "Channels" 16 156 188 (color .onAccent)
      b := label s.font b "Community" 16 222 188 (color .onAccent)
  if g.context.w > 0 then
    let x := g.context.x
    b := b.fill x 0 (x + g.context.w) h (color .panel)
    b := b.fill x 0 (x + 1) h (color .line)
    b := label s.font b (if ui.context == .settings then "Settings" else "Threads") (x + 16) 16 (g.context.w - 64) (color .fg)
    if ui.context == .threads then
      let lines := Text.layout s.font (g.context.w - 32) "Thread replies are not available in this build."
      for i in [0:lines.size] do
        b := b.line s.font lines[i]! (x + 16) (80 + i * 20) (color .muted)
  for c in scene g h ui s do
    let r := c.box
    let fill := if c.pane == .nav then
        if r.has ui.hover.1 ui.hover.2 then mixC nav 0xffffff 26 else nav
      else if r.has ui.hover.1 ui.hover.2 then color .selected else color .panel
    b := b.fill r.x r.y (r.x + r.w) (r.y + r.h) fill
    b := label s.font b c.label (r.x + 4) (r.y + (r.h - s.font.cell) / 2) (r.w - 8) (color (if c.pane == .nav then .onAccent else .fg))
  if let some bar := scrollbar g s then
    let t := bar.track
    let r := bar.thumb
    b := b.fill (t.x + 4) t.y (t.x + t.w - 2) (t.y + t.h) (color .line)
    b := b.fill r.x r.y (r.x + r.w) (r.y + r.h) (color .muted)
  return b

end Desktop
