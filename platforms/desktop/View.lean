/- Responsive composition uses the same page painters and query results as
mobile. Settings cover the right edge; the conversation retains its width. -/
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
  | send | photos | drawerAct (a : Pages.Act)
  deriving BEq, Repr, Inhabited

structure Ui where
  context : Context := .closed
  drawer : App.PageId := .you
  parents : List (App.PageId × String) := []
  stubTitle : String := ""
  switching : Bool := false
  first : Nat := 0
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
  let key := { App.pageIn s with
    page := ui.drawer, W := g.context.w,
    h := h - 60, insetTop := 0, labelText := ui.stubTitle }
  let (pg, head) := App.drawPage s.font (solid (Palette.color s.dim.theme .panel) g.context.w) none key
  let title := if ui.drawer == .stub then Appearance.leafTitle ui.stubTitle else (App.pageTitle ui.drawer).1
  (pg, if ui.parents.isEmpty then head else Appearance.header s.font s.dim g.context.w 0 title true)

def candidates (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) := Id.run do
  let mut out := []
  let add (p : Pane) (x y w h : Nat) (a : Action) (t := "") : Control Action := ⟨p, ⟨x, y, w, h⟩, a, t⟩
  -- Overlay controls precede the covered main pane in hit testing.
  if g.context.w > 0 then
    out := out ++ [add .context (g.context.x + 8) 8 44 44 .close]
    for (box, action) in (drawerPage g h ui s).1.taps do
      let y := box.y - ui.offset
      if box.y + box.h > ui.offset && y < h - 60 then
        let visibleH := min (box.y + box.h - ui.offset) (h - 60) - y
        out := out ++ [add .context (g.context.x + box.x) (60 + y) box.w visibleH (.drawerAct action)]
  if g.nav.w > 0 then
    out := out ++ [add .nav 0 0 220 56 .switcher]
    if ui.switching then
      out := out ++ [add .nav 8 60 204 36 (.page .communitySettings) "Community settings"]
      let slots := (h - 220) / 36
      for i in [ui.first:min s.comms.size (ui.first + slots)] do
        out := out ++ [add .nav 8 (104 + (i - ui.first) * 36) 204 32 (.community i) s.comms[i]!.name]
      out := out ++ [add .nav 8 (h - 100) 96 32 .previous "Previous",
        add .nav 112 (h - 100) 100 32 .next "Next",
        add .nav 8 (h - 60) 204 32 (.page .getStarted) "+ Add community"]
    else
      out := out ++ [add .nav 180 76 32 26 (.drawerAct (.stub "Create channel")),
        add .nav 0 102 220 26 (.page .chat),
        add .nav 180 160 32 26 (.drawerAct (.stub "Direct message")),
        add .nav 0 (h - 48) 220 48 .settings]
      for i in [0:s.members.size] do
        if 186 + (i + 1) * 30 > h - 48 then break
        out := out ++ [add .nav 0 (186 + i * 30) 220 30 (.drawerAct (.person i))]
  return out

def scene (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : List (Control Action) :=
  controls g h (candidates g h ui s)

/-- Compose the app's actual native layers in the main pane. -/
def content (w h : Nat) (ls : Layers) (background : Color := Row.bg) : Bitmap :=
  ⟨w, Translate.compose ls.placement (ls.placement[15]?.getD 0).toInt32 h
    (solid background w) ls.list ls.top ls.bot ls.hold, #[]⟩

def scrollbar (g : Layout) (s : App.St) : Option Scrollbar.Bar :=
  if g.main.w == 0 || g.context.w > 0 || s.page != .chat || s.sheet.isSome then none else
  Scrollbar.layout (g.main.x + g.main.w) (App.geom s).top (App.geom s).viewNow (App.bottoms s).2 s.b

def avatar (b : Bitmap) (f : Font.Font) (name id : String) (x y size : Nat) : Bitmap :=
  let b := b.round x y (x + size) (y + size) 4 (Palette.avatar id)
  let l := Text.oneLineFine f size (String.ofList [(name.toList.headD '?').toUpper])
  b.line f l (x + (size - Paint.Line.width f l) / 2) (y + (size - f.cell) / 2 + 2) 0xffffff (exactInk := true)

def paint (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (ls : Layers) : Bitmap := Id.run do
  let color := Palette.color s.dim.theme
  let nav := color .accent
  let f := s.font.atSize 14
  let mut b := Bitmap.blank g.width h (solid (color .panel) g.width)
  if g.main.w > 0 then b := b.image (content g.main.w h ls (color (if s.wide then .panel else .bg))) g.main.x 0 0
  if let some bar := scrollbar g s then
    let t := bar.track
    let r := bar.thumb
    b := b.fill (t.x + 4) t.y (t.x + t.w - 2) (t.y + t.h) (color .line)
    b := b.fill r.x r.y (r.x + r.w) (r.y + r.h) (color .muted)
  if g.nav.w > 0 then
    b := b.fill 0 0 g.nav.w h nav
    b := avatar b (s.font.atSize 16) s.me.name (Pages.identity s.me.c) 16 14 28
    let titleFont := (s.font.atSize 18).medium
    let title := Text.oneLineFine titleFont 136 s.me.name
    b := b.line titleFont title 52 21 0xffffff (exactInk := true)
    b := b.icon f "caret" (60 + Paint.Line.width titleFont title) 20 16 (mixC nav 0xffffff 205)
    let muted := mixC nav 0xffffff 179
    if ui.switching then
      for c in scene g h ui s do
        if c.pane == .nav && !c.label.isEmpty then
          b := label f b c.label (c.box.x + 8) (c.box.y + 8) (c.box.w - 16) 0xffffff
    else
      b := label f.medium b "Channels" 16 83 160 muted
      b := b.icon f "add" 188 81 16 (mixC nav 0xffffff 154)
      if s.page == .chat then b := b.fill 0 102 220 128 (mixC nav 0xffffff 51)
      let selected := if s.page == .chat then mixC nav 0xffffff 51 else nav
      b := b.icon f "hash" 16 109 12 (mixC selected 0xffffff 128)
      b := label f b "general" 32 109 168 (mixC selected 0xffffff 179)
      b := label f.medium b "Direct messages" 16 167 160 muted
      b := b.icon f "add" 188 165 16 (mixC nav 0xffffff 154)
      for i in [0:s.members.size] do
        let y := 186 + i * 30
        if y + 30 > h - 48 then break
        let (name, mine) := s.members[i]!
        b := avatar b f name (Pages.identity (s.memberIds[i]?.getD .empty)) 16 (y + 3) 24
        let nameLine := Text.oneLineFine f (if mine then 124 else 156) name
        b := b.line f nameLine 48 (y + 9) muted (exactInk := true)
        if mine then
          let asideFont := s.font.atSize 12
          let aside := (Text.oneLineFine asideFont 38 "(you)").mapIdx fun i g => { g with x := g.x + (i * 4 + 5) / 10 }
          b := b.line asideFont aside (54 + Paint.Line.width f nameLine) (y + 11) (mixC nav 0xffffff 154) (exactInk := true)
      b := b.fill 0 (h - 49) 220 (h - 48) (mixC nav 0xffffff 26)
      b := avatar b f s.ownName (Pages.identity s.me.user) 16 (h - 36) 24
      b := label f b s.ownName 48 (h - 29) 156 (mixC nav 0xffffff 161)
      -- The reference's offline ring belongs only to this device's summary.
      b := b.round 32 (h - 20) 45 (h - 7) 6 nav
      b := b.round 34 (h - 18) 43 (h - 9) 4 0xffc75a
      b := b.round 36 (h - 16) 41 (h - 11) 2 nav
  if g.context.w > 0 then
    -- A short, deterministic shadow on the covered conversation.
    for i in [0:24] do
      let x := g.context.x - 24 + i
      let alpha := (i + 1) * (i + 1) * 34 / (24 * 24)
      for y in [0:h] do
        b := b.modify y fun row => setPx row x (mixC (getPx row x) 0 alpha)
    let (pg, head) := drawerPage g h ui s
    b := b.image { pg.bmp with rows := pg.bmp.rows.extract ui.offset (ui.offset + h - 60) } g.context.x 60 0
    b := b.image head g.context.x 0 0
    b := b.fill g.context.x 0 (g.context.x + 1) h (color .selected)
  return b

end Desktop
