/- Responsive composition uses the same page painters and query results as
mobile. Settings cover the right edge; the conversation retains its width. -/
import platforms.desktop.Switcher
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
  | page (p : App.PageId)
  | send | photos | drawerAct (a : Pages.Act) | popup (a : Switcher.Act)
  deriving BEq, Repr, Inhabited

structure Ui where
  context : Context := .closed
  drawer : App.PageId := .you
  parents : List (App.PageId × String) := []
  stubTitle : String := ""
  switching : Bool := false
  switchOffset : Nat := 0
  offset : Nat := 0
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
  b.line f (Text.oneLineFine f w s) x y color (exactInk := true)

/-- The drawer's key includes its own observed profile/counts and theme.
Its background conversation is never resized to make room for it. -/
def drawerPage (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : Pages.Page × Bitmap :=
  let px := s.dim.px
  let key := { App.pageIn s with
    page := ui.drawer, W := g.context.w,
    h := h - (px 60), insetTop := 0, labelText := ui.stubTitle }
  let (pg, head) := App.drawPage s.font (solid (Palette.color s.dim.theme .panel) g.context.w) none key
  let title := if ui.drawer == .stub then Appearance.leafTitle ui.stubTitle else (App.pageTitle ui.drawer).1
  (pg, if ui.parents.isEmpty then head else Appearance.header s.font s.dim g.context.w 0 title true)

def candidates (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) := Id.run do
  let px := s.dim.px
  let mut out := []
  let add (p : Pane) (x y w h : Nat) (a : Action) (t := "") : Control Action := ⟨p, ⟨x, y, w, h⟩, a, t⟩
  if ui.switching && g.nav.w > 0 then
    return (Switcher.candidates s (Switcher.model s h ui.switchOffset)).map fun c =>
      { c with action := .popup c.action }
  -- Overlay controls precede the covered main pane in hit testing.
  if g.context.w > 0 then
    out := out ++ [add .context (g.context.x + (px 8)) (px 8) (px 44) (px 44) .close]
    for (box, action) in (drawerPage g h ui s).1.taps do
      let y := box.y - ui.offset
      if box.y + box.h > ui.offset && y < h - (px 60) then
        let visibleH := min (box.y + box.h - ui.offset) (h - (px 60)) - y
        out := out ++ [add .context (g.context.x + box.x) ((px 60) + y) box.w visibleH (.drawerAct action)]
  if g.nav.w > 0 then
    out := out ++ [add .nav 0 0 (px 220) (px 56) .switcher]
    out := out ++ [add .nav (px 180) (px 76) (px 32) (px 26) (.drawerAct (.stub "Create channel")),
      add .nav 0 (px 102) (px 220) (px 26) (.page .chat),
      add .nav (px 180) (px 160) (px 32) (px 26) (.drawerAct (.stub "Direct message")),
      add .nav 0 (h - (px 48)) (px 220) (px 48) .settings]
    for i in [0:s.members.size] do
      if (px 186) + (i + 1) * (px 30) > h - (px 48) then break
      out := out ++ [add .nav 0 ((px 186) + i * (px 30)) (px 220) (px 30) (.drawerAct (.person i))]
  return out

def scene (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) :=
  controls g h (candidates g h ui s) (max 1 (s.dim.px 24))

/-- Compose the app's actual native layers in the main pane. -/
def content (w h : Nat) (ls : Layers) (background : Color := Row.bg) : Bitmap :=
  ⟨w, Translate.compose ls.placement (ls.placement[15]?.getD 0).toInt32 h
    (solid background w) ls.list ls.top ls.bot ls.hold, #[]⟩

def scrollbar (g : Layout) (s : App.St) : Option Scrollbar.Bar :=
  if g.main.w == 0 || g.context.w > 0 || s.page != .chat || s.sheet.isSome then none else
  Scrollbar.layout (g.main.x + g.main.w) (App.geom s).top (App.geom s).viewNow (App.bottoms s).2 s.b s.dim.dpi

def avatar (b : Bitmap) (f : Font.Font) (name id : String) (x y size : Nat)
    (radius := 4) (baseline := 2) : Bitmap :=
  let b := b.round x y (x + size) (y + size) radius (Palette.avatar id)
  let l := Text.oneLineFine f size (String.ofList [(name.toList.headD '?').toUpper])
  b.line f l (x + (size - Paint.Line.width f l) / 2) (y + (size - f.cell) / 2 + baseline) 0xffffff (exactInk := true)

def paint (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (ls : Layers) : Bitmap := Id.run do
  let px := s.dim.px
  let color := Palette.color s.dim.theme
  let nav := color .accent
  let f := s.font.atSize (px 14)
  let mut b := Bitmap.blank g.width h (solid (color .panel) g.width)
  if g.main.w > 0 then b := b.image (content g.main.w h ls (color (if s.wide then .panel else .bg))) g.main.x 0 0
  if let some bar := scrollbar g s then
    let t := bar.track
    let r := bar.thumb
    b := b.fill (t.x + px 4) t.y (t.x + t.w - px 2) (t.y + t.h) (color .line)
    b := b.fill r.x r.y (r.x + r.w) (r.y + r.h) (color .muted)
  if g.nav.w > 0 then
    b := b.fill 0 0 g.nav.w h nav
    b := avatar b (s.font.atSize (px 16)) s.me.name (Pages.identity s.me.c) (px 16) (px 14) (px 28) (px 4) (px 2)
    let titleFont := (s.font.atSize (px 18)).medium
    let title := Text.oneLineFine titleFont (px 136) s.me.name
    b := b.line titleFont title (px 52) (px 21) 0xffffff (exactInk := true)
    b := b.icon f "caret" ((px 60) + Paint.Line.width titleFont title) (px 20) (px 16) (mixC nav 0xffffff 205)
    let muted := mixC nav 0xffffff 179
    b := label f.medium b "Channels" (px 16) (px 83) (px 160) muted
    b := b.icon f "add" (px 188) (px 81) (px 16) (mixC nav 0xffffff 154)
    if s.page == .chat then b := b.fill 0 (px 102) (px 220) (px 128) (mixC nav 0xffffff 51)
    let selected := if s.page == .chat then mixC nav 0xffffff 51 else nav
    b := b.icon f "hash" (px 16) (px 109) (px 12) (mixC selected 0xffffff 128)
    b := label f b "general" (px 32) (px 109) (px 168) (mixC selected 0xffffff 179)
    b := label f.medium b "Direct messages" (px 16) (px 167) (px 160) muted
    b := b.icon f "add" (px 188) (px 165) (px 16) (mixC nav 0xffffff 154)
    for i in [0:s.members.size] do
      let y := (px 186) + i * (px 30)
      if y + (px 30) > h - (px 48) then break
      let (name, mine) := s.members[i]!
      b := avatar b f name (Pages.identity (s.memberIds[i]?.getD .empty)) (px 16) (y + (px 3)) (px 24) (px 4) (px 2)
      let nameLine := Text.oneLineFine f (if mine then (px 124) else (px 156)) name
      b := b.line f nameLine (px 48) (y + (px 9)) muted (exactInk := true)
      if mine then
        let asideFont := s.font.atSize (px 12)
        let aside := (Text.oneLineFine asideFont (px 38) "(you)").mapIdx fun i g => { g with x := g.x + (i * 4 * s.dim.dpi + 800) / 1600 }
        b := b.line asideFont aside ((px 54) + Paint.Line.width f nameLine) (y + (px 11)) (mixC nav 0xffffff 154) (exactInk := true)
    b := b.fill 0 (h - (px 49)) (px 220) (h - (px 48)) (mixC nav 0xffffff 26)
    b := avatar b f s.ownName (Pages.identity s.me.user) (px 16) (h - (px 36)) (px 24) (px 4) (px 2)
    b := label f b s.ownName (px 48) (h - (px 29)) (px 156) (mixC nav 0xffffff 161)
    -- The reference's offline ring belongs only to this device's summary.
    b := b.round (px 32) (h - (px 20)) (px 45) (h - (px 7)) (px 6) nav
    b := b.round (px 34) (h - (px 18)) (px 43) (h - (px 9)) (px 4) 0xffc75a
    b := b.round (px 36) (h - (px 16)) (px 41) (h - (px 11)) (px 2) nav
  if g.context.w > 0 then
    -- The shell's settings panel has a hairline, not the floating drawer's
    -- shadow (libquiet ContextPanel / .drawer.embedded).
    let (pg, head) := drawerPage g h ui s
    b := b.image { pg.bmp with rows := pg.bmp.rows.extract ui.offset (ui.offset + h - (px 60)) } g.context.x (px 60) 0
    b := b.image head g.context.x 0 0
    b := b.fill g.context.x 0 (g.context.x + px 1) h (color .selected)
  if ui.switching && g.nav.w > 0 then
    b := Switcher.paint b s (Switcher.model s h ui.switchOffset) ui.hover
  return b

end Desktop
