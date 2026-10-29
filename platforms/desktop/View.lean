/-
The desktop root: the existing app's pixels in a fluid middle track,
community navigation on the left, and a settings/threads context on the
right. Controls are painted and dispatched from Layout.controls. The
threads surface reports the missing reply domain honestly.
-/
import App
import engine.renderer.TranslatePaint
import engine.renderer.desktop.Layout

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
  if g.main.w > 0 then
    let x := g.main.x
    if g.nav.w == 0 then
      out := out ++ [add .main x 4 112 32 .switcher "Communities"]
    out := out ++ [add .main (x + g.main.w - 168) 4 80 32 .threads "Threads",
      add .main (x + g.main.w - 88) 4 80 32 .settings "Settings"]
    if s.page == .chat && s.sheet.isNone then
      out := out ++ [add .main (x + 8) (h - 52) 112 40 .photos "Add photos",
        add .main (x + g.main.w - 88) (h - 52) 80 40 .send "Send"]
  if g.context.w > 0 then
    let x := g.context.x
    out := out ++ [add .context (x + g.context.w - 40) 8 32 32 .close "x"]
    if ui.context == .settings then
      out := out ++ [add .context (x + 16) 80 (g.context.w - 32) 48 (.page .invite) "Add members",
        add .context (x + 16) 136 (g.context.w - 32) 48 (.page .requests) "Join requests",
        add .context (x + 16) 192 (g.context.w - 32) 48 (.page .home) "People",
        add .context (x + 16) 248 (g.context.w - 32) 48 (.page .switcher) "Communities"]
  return out

def scene (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) :=
  controls g h (candidates g h ui s)

/-- Compose the app's actual three layers, in their own track. -/
def content (w h : Nat) (ls : Layers) : Bitmap :=
  ⟨w, Translate.compose ls.placement (ls.placement[15]?.getD 0).toInt32 h
    (solid Row.bg w) ls.list ls.top ls.bot ls.hold, #[]⟩

/-- Painting traverses exactly `scene`, the list hit testing consumes. -/
def paint (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (ls : Layers) : Bitmap := Id.run do
  let mut b := Bitmap.blank g.width h (solid Row.bg g.width)
  if g.main.w > 0 then
    b := b.image (content g.main.w (h - 40) ls) g.main.x 40 0
    b := b.fill g.main.x 0 (g.main.x + g.main.w) 40 0x16181B
    if s.page == .chat && s.sheet.isNone then
      -- The phone's six 48px icons do not fit a 275px track. Keep the
      -- working desktop actions, with distinct, contained hit boxes.
      b := b.fill g.main.x (h - 60) (g.main.x + g.main.w) h Row.bg
      let c := App.composerLayout s
      let a := min s.sel[0]!.toNat s.sel[1]!.toNat
      let z := max s.sel[0]!.toNat s.sel[1]!.toNat
      for i in [a:min s.text.length z] do
        let (r, x) := App.cursorAt s i
        let (r', x') := App.cursorAt s (i + 1)
        if r < 5 then
          let x0 := g.main.x + c.textX + x
          let x1 := min (g.main.x + c.textX + c.textW) (if r == r' then g.main.x + c.textX + x' else x0 + 8)
          let y0 := h - App.botH s + c.textY + r * s.dim.lineH
          for y in [y0:min h (y0 + s.font.cell)] do
            b := b.modify y fun row => Id.run do
              let mut row := row
              for px in [x0:x1] do row := Paint.setPx row px (Paint.mixC (Paint.getPx row px) 0x4488CC 100)
              return row
  if g.nav.w > 0 then
    b := b.fill 0 0 g.nav.w h purple
    if !ui.switching then
      b := label s.font b "Channels" 16 156 188
      b := label s.font b "Community" 16 222 188
  if g.context.w > 0 then
    let x := g.context.x
    b := b.fill x 0 (x + g.context.w) h Pages.card
    b := b.fill x 0 (x + 1) h Pages.cardLine
    b := label s.font b (if ui.context == .settings then "Settings" else "Threads") (x + 16) 16 (g.context.w - 64)
    if ui.context == .threads then
      let lines := Text.layout s.font (g.context.w - 32) "Thread replies are not available in this build."
      for i in [0:lines.size] do
        b := b.line s.font lines[i]! (x + 16) (80 + i * 20) Row.dim
  for c in scene g h ui s do
    let r := c.box
    let color := if c.pane == .nav then
        if r.has ui.hover.1 ui.hover.2 then hoverColor else purple
      else if r.has ui.hover.1 ui.hover.2 then Pages.cardLine else Pages.card
    b := b.fill r.x r.y (r.x + r.w) (r.y + r.h) color
    b := label s.font b c.label (r.x + 4) (r.y + (r.h - s.font.cell) / 2) (r.w - 8)
  return b

end Desktop
