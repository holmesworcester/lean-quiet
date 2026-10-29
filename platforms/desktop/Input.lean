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
  if s.page != .chat || g.main.w == 0 || x < x0 || x ≥ x0 + c.textW ||
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
  (scrollbar d.layout d.app).bind fun bar => Scrollbar.grab bar x y

def scrollDrag (d : Driver) (grab y : Nat) : IO Unit := do
  if let some bar := scrollbar d.layout d.app then
    d.app.io.scrollTo (Scrollbar.offset bar grab y).toFloat

end Desktop
