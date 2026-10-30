/-
Pointer selection in the running composer's laid-out text. It uses
App.cursorAt, the same caret positions the composer paints. The native
editor owns the UTF-8 buffer; this module returns code-point boundaries.
-/
import platforms.desktop.Driver

namespace Desktop

def caret (d : Driver) (x y : Nat) : Option Nat := Id.run do
  let g := d.layout
  let s := d.app
  let c := App.composerLayout s
  let x0 := g.main.x + c.textX
  let y0 := d.height - App.botH s + c.textY
  if d.ui.switching || s.page != .chat || g.main.w == 0 || x < x0 || x ≥ x0 + c.textW ||
      (g.context.w > 0 && x ≥ g.context.x) || y < y0 || y ≥ y0 + min 5 c.lines.size * c.lineH then return none
  let row := (y - y0) / c.lineH
  let px := x - x0
  let mut best := 0
  let mut distance := 1000000
  for i in [0:s.text.length + 1] do
    let (r, cx) := App.cursorAt s i
    let delta := (if row > r then row - r else r - row) * (s.W + 1) +
      (if px > cx then px - cx else cx - px)
    if delta < distance then
      best := i
      distance := delta
  return some best

def scrollGrab (d : Driver) (x y : Nat) : Option Nat :=
  if d.ui.switching then none else
  (scrollbar d.layout d.app).bind fun bar => Scrollbar.grab bar x y

def scrollDrag (d : Driver) (grab y : Nat) : IO Unit := do
  if let some bar := scrollbar d.layout d.app then
    d.app.io.scrollTo (Scrollbar.offset bar grab y).toFloat

/-- Native cursor choice follows the same topmost hit geometry as actions.
No pointer is synthesized from a touch or from a window's initial (0,0). -/
def cursor (d : Driver) : Nat := Id.run do
  let some (x, y) := d.ui.hover | return 0
  let g := d.layout
  if (messageAction g d.height d.ui d.app x y).isSome then return 1
  if let some (id, _, _, _) := hoveredRow g d.height d.ui d.app then
    if (messageBar g d.height d.app id).any (·.has x y) ||
        (d.ui.moreFor == some id && (messageMenu g d.height d.app id).any (·.has x y)) then return 0
  if (authorAt g d.height d.ui d.app x y).isSome then return 1
  if (hit (scene g d.height d.ui d.app) x y).isSome then return 1
  if d.ui.switching || (g.context.w > 0 && x ≥ g.context.x) then return 0
  let some (x, y) := Hover.within (pointer g d.height d.ui .main) ⟨g.main.x, 0, g.main.w, d.height⟩ | return 0
  let s := d.app
  if !s.notices.isEmpty then return 1
  if s.page != .chat then
    if y < App.topH s then return if x < s.dim.px 56 then 1 else 0
    let pg := match s.pageNow with
      | some pg => pg
      | none => (App.drawPage s.font s.bgRow s.camView (App.pageIn s)).1
    let offset := if s.page.drawer then pg.bmp.h - App.viewH s - s.b else 0
    let a := pg.hit x (y - App.topH s + offset)
    return if a == .field then 2 else if a != .none then 1 else 0
  if y < App.topH s then
    return if (!s.wide && x < s.dim.px 56) || Hover.active (some (x, y)) ⟨s.W - s.dim.px (if s.wide then 52 else 46), s.insetTop + s.dim.px (if s.wide then 16 else 14), s.dim.px 32, s.dim.px 32⟩ then 1 else 0
  if y ≥ d.height - App.botH s then
    if let some sh := s.sheet then
      if sh.catalog then
        let a := Sheet.hitCat (App.catOf s sh) sh.scroll x (y - (d.height - App.botH s))
        return match a with
          | .search => 2
          | .pick i => if i < (App.sheetItems s sh).size then 1 else 0
          | .none => 0
          | _ => 1
      return if Sheet.hitQuick s.dim s.W x (y - (d.height - App.botH s)) != .none then 1 else 0
    let hit := Composer.hit (App.composerLayout s) x (y - (d.height - App.botH s))
    return if hit == .text then 2 else if hit == .none || (hit == .send && s.text.trimAscii.isEmpty && s.chips.isEmpty) then 0 else 1
  if s.sheet.isSome then return 0
  let some (id, ry) := App.rowAt s (s.b + d.height - App.botH s - 1 - y) | return 0
  let some row := s.rows[id]? | return 0
  -- Messages are read-only until transcript selection is implemented.
  return if Row.hit row.lay x ry != .row then 1 else 0

end Desktop
