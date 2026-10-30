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
  hover : Hover.Context := none
  hoverRow : Option ByteArray := none
  moreFor : Option ByteArray := none
  tooltip : Bool := false
  hoverFrom : Hover.Context := none
  grace : Bool := false
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

/-- The paint route is the same front-to-back order as hit dispatch.
The popup's clear dismiss surface covers the whole window, not only its card. -/
def surfaces (g : Layout) (h : Nat) (ui : Ui) : List (Pane × Hover.Box) :=
  (if ui.switching then [(.overlay, ⟨0, 0, g.width, h⟩)] else []) ++
  (if g.context.w > 0 then [(.context, ⟨g.context.x, 0, g.context.w, h⟩)] else []) ++
  (if g.nav.w > 0 then [(.nav, ⟨0, 0, g.nav.w, h⟩)] else []) ++
  [(.main, ⟨g.main.x, 0, g.main.w, h⟩)]

def pointer (g : Layout) (h : Nat) (ui : Ui) (pane : Pane) : Hover.Context :=
  Hover.routed ui.hover (surfaces g h ui) pane

/-- The drawer's key includes its own observed profile/counts and theme.
Its background conversation is never resized to make room for it. -/
def drawerPage (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : Pages.Page × Bitmap :=
  let px := s.dim.px
  let hp := Hover.within (pointer g h ui .context) ⟨g.context.x, px 60, g.context.w, h - px 60⟩
  let key := { App.pageIn s with
    dim := { s.dim with hover := Hover.move hp 0 ui.offset },
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

/-- Native scrolling covers only the visible conversation, never fixed chrome
or a right-hand drawer. The shell consumes this published device-pixel box. -/
def scrollViewport (g : Layout) (_h : Nat) (ui : Ui) (s : App.St) (ls : Layers) : Array UInt32 := Id.run do
  let right := min (g.main.x + g.main.w) (if g.context.w > 0 then g.context.x else g.width)
  let geom := App.geom s
  let active := s.page == .chat && !ui.switching && s.notices.isEmpty &&
    right > g.main.x && geom.viewNow > 0 && !ls.list.isEmpty && ls.placement.size ≥ 29 &&
    (ls.placement[22]?.getD 1) == 0
  return #[(if active then 1 else 0), g.main.x.toUInt32, geom.top.toUInt32,
    (right - g.main.x).toUInt32, geom.viewNow.toUInt32, (App.bottoms s).2.toUInt32]

def avatar (b : Bitmap) (f : Font.Font) (name id : String) (x y size : Nat)
    (radius := 4) (baseline := 2) : Bitmap :=
  let b := b.round x y (x + size) (y + size) radius (Palette.avatar id)
  let l := Text.oneLineFine f size (String.ofList [(name.toList.headD '?').toUpper])
  b.line f l (x + (size - Paint.Line.width f l) / 2) (y + (size - f.cell) / 2 + baseline) 0xffffff (exactInk := true)

/-- Derived from the current list, so scroll/resize never leaves stale targets. -/
def messageTop (s : App.St) (h : Nat) (id : ByteArray) : Option Int := do
  let i ← s.ids.findIdx? (·.2 == id)
  let bot ← (App.bottoms s).1[i]?
  return Int.ofNat (s.b + h - App.botH s) - (bot + App.heightOf s id)

def messageBar (g : Layout) (h : Nat) (s : App.St) (id : ByteArray) : Option Box := do
  let top ← messageTop s h id
  if top + App.heightOf s id ≤ App.topH s || top ≥ h - App.botH s then none else
    some ⟨g.main.x + g.main.w - s.dim.px 142,
      max (App.topH s + s.dim.px 8) (top - s.dim.px 16).toNat, s.dim.px 134, s.dim.px 48⟩

def messageMenu (g : Layout) (h : Nat) (s : App.St) (id : ByteArray) : Option Box := do
  let bar ← messageBar g h s id
  let height := s.dim.px (if s.rows[id]?.any (·.data.own) then 96 else 52)
  return ⟨bar.x + bar.w - s.dim.px 178,
    if bar.y + s.dim.px 40 + height > h - App.botH s then bar.y - height - s.dim.px 4 else bar.y + s.dim.px 40,
    s.dim.px 178, height⟩

def hoveredRow (g : Layout) (h : Nat) (ui : Ui) (s : App.St) : Option (ByteArray × Nat × Nat × Nat) := do
  let (x, y) ← Hover.within (pointer g h ui .main) ⟨g.main.x, 0, g.main.w, h⟩
  if s.page != .chat || s.sheet.isSome || !s.notices.isEmpty || y < App.topH s || y ≥ h - App.botH s then none else do
    if let some id := ui.moreFor <|> ui.hoverRow then
      if (ui.moreFor == some id || ui.grace || (messageBar g h s id).any (·.has (g.main.x + x) y)) && (messageBar g h s id).isSome then
        let top ← messageTop s h id
        return (id, x, y, (Int.ofNat y - top).toNat)
    let (id, ry) ← App.rowAt s (s.b + h - App.botH s - 1 - y)
    return (id, x, y, ry)

/-- Author identity comes from the rendered message op and the mounted
membership/profile component; the name and avatar share their hit geometry. -/
def authorAt (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (x y : Nat) : Option Nat := do
  let ui := { ui with hover := some (x, y), hoverRow := none, moreFor := none, grace := false }
  let (id, x, _, ry) ← hoveredRow g h ui s
  let row ← s.rows[id]?
  if row.data.clump.isSome then none else do
    let dm := s.dim
    let hy := Row.headY dm row.data
    let avatar : Row.Box := ⟨dm.pad, hy + dm.px 6, dm.avatar, dm.avatar⟩
    let name : Row.Box := ⟨dm.textX, hy + dm.px 3, Paint.Line.width (s.font.atSize (dm.px 16)) row.lay.name, dm.px 24⟩
    if avatar.has x ry || name.has x ry then s.memberIds.findIdx? (· == row.data.author) else none

inductive MessageAction where
  | react | thread | more | edit | copy
  deriving BEq, Repr

def messageAction (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (x y : Nat) : Option (ByteArray × MessageAction) := do
  let (id, _, _, _) ← hoveredRow g h ui s
  let px := s.dim.px
  if ui.moreFor == some id then
    if let some menu := messageMenu g h s id then
      let own := s.rows[id]?.any (·.data.own)
      if own && (⟨menu.x + px 4, menu.y + px 4, px 170, px 44⟩ : Box).has x y then return (id, .edit)
      if (⟨menu.x + px 4, menu.y + px (if own then 48 else 4), px 170, px 44⟩ : Box).has x y &&
          s.rows[id]?.any (! ·.data.text.isEmpty) then return (id, .copy)
  let bar ← messageBar g h s id
  if (⟨bar.x + px 12, bar.y + px 8, px 38, px 32⟩ : Box).has x y then some (id, .react)
  else if (⟨bar.x + px 56, bar.y + px 2, px 36, px 44⟩ : Box).has x y then some (id, .thread)
  else if (⟨bar.x + px 92, bar.y + px 2, px 36, px 44⟩ : Box).has x y then some (id, .more)
  else none

def paintMessageBar (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (b : Bitmap) : Bitmap := Id.run do
  let some (id, _, _, _) := hoveredRow g h ui s | return b
  let some bar := messageBar g h s id | return b
  let px := s.dim.px
  let color := Palette.color s.dim.theme
  let hp := pointer g h ui .main
  let hot (x y w h : Nat) := Hover.active hp ⟨x, y, w, h⟩
  let mut b := Switcher.shadow b s.dim bar 30 6 0.10
  b := b.round bar.x bar.y (bar.x+bar.w) (bar.y+bar.h) (px 16) (color .panel)
  let x := bar.x + px 12
  let y := bar.y + px 8
  let border := if hot x y (px 38) (px 32) then color .accentInk else color .selected
  b := b.round x y (x+px 38) (y+px 32) (px 16) border
  b := b.round (x+px 1) (y+px 1) (x+px 37) (y+px 31) (px 15) (color .selected)
  b := b.icon s.font "emoji-add" (x+px 8) (y+px 5) (px 22) (if s.dim.theme == .dark then 0xa0a0a0 else 0x7f7f7f)
  for (icon, offset) in [("thread-action", 62), ("more", 98)] do
    let ink := if hot (bar.x+px (offset-6)) (bar.y+px 2) (px 36) (px 44) || (icon == "more" && ui.moreFor == some id) then color .fg else if s.dim.theme == .dark then 0xa0a0a0 else 0x7f7f7f
    b := b.icon s.font icon (bar.x+px offset) (bar.y+px 12) (px 24) ink
  if ui.tooltip && ui.moreFor.isNone then
    if let some (mx, my) := hp then
      if let some (_, action) := messageAction g h ui s mx my then
        let title := match action with | .react => "Add a reaction" | .thread => "Reply in thread" | .more => "More actions" | _ => ""
        if !title.isEmpty then
          let font := s.font.atSize (px 14)
          let text := Text.oneLineFine font (px 193) title
          let tw := Paint.Line.width font text + px 32
          let center := bar.x + px (if action == .react then 31 else if action == .thread then 74 else 110)
          let tx := min (b.w - tw) (if action == .more then bar.x + bar.w - px 12 - tw else center - tw / 2)
          let ty := bar.y - px (if action == .react then 41 else 37)
          -- libquiet's semantic black/white invert with the theme.
          let ground := if s.dim.theme == .light then 0x222222 else 0xeaeaea
          let ink := if s.dim.theme == .light then 0xffffff else 0x222222
          b := b.round tx ty (tx+tw) (ty+px 37) (px 8) ground
          for j in [0:px 7] do
            let half := px 5 * (px 7 - j) / max 1 (px 7)
            b := b.fill (center-half) (ty+px 36+j) (center+half) (ty+px 37+j) ground
          b := b.line font text (tx+px 16) (ty+px 12) ink (exactInk := true)
  if ui.moreFor == some id then
    if let some menu := messageMenu g h s id then
      b := Switcher.shadow b s.dim menu 30 6 0.10 8
      b := b.round menu.x menu.y (menu.x+menu.w) (menu.y+menu.h) (px 8) (color .panel)
      let entries := if s.rows[id]?.any (·.data.own) then [("Edit message", 4), ("Copy text", 48)] else [("Copy text", 4)]
      for (text, offset) in entries do
        let enabled := text == "Edit message" || s.rows[id]?.any (! ·.data.text.isEmpty)
        if enabled && hot (menu.x+px 4) (menu.y+px offset) (px 170) (px 44) then
          b := b.round (menu.x+px 4) (menu.y+px offset) (menu.x+px 174) (menu.y+px (offset+44)) (px 4) (color .selected)
        b := label (s.font.atSize (px 14)) b text (menu.x+px 12) (menu.y+px (offset+12)) (px 154) (color (if enabled then .fg else .muted))
  return b

/-- The sheet shares its own key geometry with the touch painter. Only a
hovered catalogue row is repainted; the rest keeps its existing grid cache. -/
def paintSheetHover (s : App.St) (sh : App.SheetSt) (hp : Hover.Context) : Bitmap := Id.run do
  let dm := { s.dim with hover := hp }
  let backdrop := Palette.color s.dim.theme .bg
  let mine := s.selected.map (App.mineOn s) |>.getD []
  if !sh.catalog then return Sheet.paintQuick s.font dm s.W backdrop mine
  let c := App.catOf s sh
  let items := App.sheetItems s sh
  let top := Sheet.catTop s.font dm s.W c backdrop sh.query sh.searching sh.tone sh.cat
  let botDm := { dm with hover := Hover.within hp ⟨0, c.grid.y0 + c.grid.vh, s.W, c.h - c.grid.y0 - c.grid.vh⟩ }
  let bot := Sheet.catBot s.font botDm s.W c sh.cat sh.searching
  let gp := Hover.move (Hover.within hp ⟨0, c.grid.y0, s.W, c.grid.vh⟩) 0 sh.scroll
  let hovered := gp.map fun p => p.2 / max 1 c.grid.key
  let row := hovered.map fun r => Sheet.gridRow s.font { dm with hover := gp.map fun p => (p.1, p.2 % max 1 c.grid.key) } s.W c s.catalog items sh.tone mine r
  let line := fun y =>
    let r := y / max 1 c.grid.key
    let bmp := if hovered == some r then row else s.gridRows[r]?
    (bmp.bind fun b => b.rows[y % max 1 c.grid.key]?).getD (Paint.solid (Palette.color s.dim.theme .panel) s.W)
  return ⟨s.W, SheetGeom.compose top.rows line c.grid.vh sh.scroll bot.rows, #[]⟩

/-- A hovered component paints from its existing answers/decoded images.
No subscriptions, row caches, or native editor state are changed by painting. -/
def paintMainHover (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (b : Bitmap) (rowPaint : Option Bitmap := none) : Bitmap := Id.run do
  let hp := Hover.within (pointer g h ui .main) ⟨g.main.x, 0, g.main.w, h⟩
  let some (x, y) := hp | return b
  if !s.notices.isEmpty then return b
  let th := App.topH s
  let bh := App.botH s
  if s.page != .chat then
    let old := match s.pageNow with
      | some pg => pg
      | none => (App.drawPage s.font s.bgRow s.camView (App.pageIn s)).1
    let offset := if s.page.drawer then old.bmp.h - App.viewH s - s.b else 0
    if y < th then return b -- shared back/close glyphs have no visual hover
    let dm := { s.dim with hover := some (x, y - th + offset) }
    let pg := (App.drawPage s.font s.bgRow s.camView { App.pageIn s with dim := dm }).1
    return b.image { pg.bmp with rows := pg.bmp.rows.extract offset (offset + h - th - bh) } g.main.x th 0
  if let some sh := s.sheet then
    if y < h - bh then return b
    return b.image (paintSheetHover s sh (some (x, y - (h - bh)))) g.main.x (h - bh) 0
  if y < th then return b.image (App.header { s with dim := { s.dim with hover := hp } }) g.main.x 0 0
  if y ≥ h - bh then
    let dm := { s.dim with hover := some (x, y - (h - bh)) }
    return b.image (App.composer { s with dim := dm }) g.main.x (h - bh) 0
  let some (id, _, _, ry) := hoveredRow g h ui s | return b
  let some row := s.rows[id]? | return b
  let some inputs := row.pixels | return b
  if !(row.shown.any (·.w == s.W)) then return b
  let dm := { s.dim with hover := some (x, ry) }
  let bmp := match rowPaint with
    | some bmp => bmp
    | none => Row.paint s.font dm s.W s.bgRow inputs.data inputs.lay none inputs.images
  let some top := messageTop s h id | return b
  let clipTop := max (Int.ofNat th) top
  let clipBottom := min (Int.ofNat (h - bh)) (top + bmp.h)
  let clipped := { bmp with rows := bmp.rows.extract (clipTop - top).toNat (clipBottom - top).toNat }
  return b.image clipped g.main.x clipTop.toNat 0

def paint (g : Layout) (h : Nat) (ui : Ui) (s : App.St) (ls : Layers) (rowPaint : Option Bitmap := none) (nativeScroll : Bool := false) : Bitmap := Id.run do
  let px := s.dim.px
  let color := Palette.color s.dim.theme
  let nav := color .accent
  let navPointer := pointer g h ui .nav
  let hot (x y w h : Nat) := Hover.active navPointer ⟨x, y, w, h⟩
  let f := s.font.atSize (px 14)
  let mut b := Bitmap.blank g.width h (solid (color .panel) g.width)
  if g.main.w > 0 then b := b.image (content g.main.w h ls (color (if s.wide then .panel else .bg))) g.main.x 0 0
  b := paintMainHover g h ui s b rowPaint
  b := paintMessageBar g h ui s b
  if let some bar := (if nativeScroll then none else scrollbar g s) then
    let t := bar.track
    let r := bar.thumb
    b := b.fill (t.x + px 4) t.y (t.x + t.w - px 2) (t.y + t.h) (color .line)
    b := b.fill r.x r.y (r.x + r.w) (r.y + r.h) (color .muted)
  if g.nav.w > 0 then
    b := b.fill 0 0 g.nav.w h nav
    if hot (px 16) (px 12) (px 188) (px 32) then
      b := b.round (px 16) (px 12) (px 204) (px 44) (px 6) (mixC nav 0xffffff 13)
    b := avatar b (s.font.atSize (px 16)) s.me.name (Pages.identity s.me.c) (px 16) (px 14) (px 28) (px 4) (px 2)
    let titleFont := (s.font.atSize (px 18)).medium
    let title := Text.oneLineFine titleFont (px 136) s.me.name
    b := b.line titleFont title (px 52) (px 21) 0xffffff (exactInk := true)
    b := b.icon f "caret" ((px 60) + Paint.Line.width titleFont title) (px 20) (px 16) (mixC nav 0xffffff 205)
    let muted := mixC nav 0xffffff 179
    b := label f.medium b "Channels" (px 16) (px 83) (px 160) muted
    b := b.icon f "add" (px 188) (px 81) (px 16) (mixC nav 0xffffff (if hot (px 180) (px 76) (px 32) (px 26) then 256 else 154))
    if s.page == .chat then b := b.fill 0 (px 102) (px 220) (px 128) (mixC nav 0xffffff 51)
    if s.page != .chat && hot 0 (px 102) (px 220) (px 26) then b := b.fill 0 (px 102) (px 220) (px 128) (mixC nav 0xffffff 13)
    let selected := if s.page == .chat then mixC nav 0xffffff 51 else nav
    b := b.icon f "hash" (px 16) (px 109) (px 12) (mixC selected 0xffffff 128)
    b := label f b "general" (px 32) (px 109) (px 168) (mixC selected 0xffffff 179)
    b := label f.medium b "Direct messages" (px 16) (px 167) (px 160) muted
    b := b.icon f "add" (px 188) (px 165) (px 16) (mixC nav 0xffffff (if hot (px 180) (px 160) (px 32) (px 26) then 256 else 154))
    for i in [0:s.members.size] do
      let y := (px 186) + i * (px 30)
      if y + (px 30) > h - (px 48) then break
      if hot 0 y (px 220) (px 30) then b := b.fill 0 y (px 220) (y + px 30) (mixC nav 0xffffff 13)
      let (name, mine) := s.members[i]!
      b := avatar b f name (Pages.identity (s.memberIds[i]?.getD .empty)) (px 16) (y + (px 3)) (px 24) (px 4) (px 2)
      let nameLine := Text.oneLineFine f (if mine then (px 124) else (px 156)) name
      b := b.line f nameLine (px 48) (y + (px 9)) muted (exactInk := true)
      if mine then
        let asideFont := s.font.atSize (px 12)
        let aside := (Text.oneLineFine asideFont (px 38) "(you)").mapIdx fun i g => { g with x := g.x + (i * 4 * s.dim.dpi + 800) / 1600 }
        b := b.line asideFont aside ((px 54) + Paint.Line.width f nameLine) (y + (px 11)) (mixC nav 0xffffff 154) (exactInk := true)
    if hot 0 (h - px 48) (px 220) (px 48) then b := b.fill 0 (h - px 48) (px 220) h (mixC nav 0xffffff 13)
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
