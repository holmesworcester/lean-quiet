import engine.renderer.Row
import engine.renderer.Overlay
import engine.renderer.Label

/-!
The page toolkit: boxes, a page (a picture and the boxes a tap can
land on, each with its action), and the pieces pages are drawn from
(rows, buttons, fields, bars, toasts, badges). Generic in the action: a
page reports what its caller gave it.
-/

namespace Pages
open Paint Text Font Row

def identity (id : ByteArray) : String := String.join (id.toList.map fun b =>
  let h := String.ofList (Nat.toDigits 16 b.toNat)
  if h.length < 2 then "0" ++ h else h)

/-! ## Theme (libquiet's dark Stage) -/

def card : Color := Palette.color .dark .panel

def cardLine : Color := Palette.color .dark .edge

def primary : Color := Palette.color .dark .button

def primaryInk : Color := Palette.color .dark .onAccent

def link : Color := Palette.color .dark .link

def logo : Color := Palette.color .dark .accentInk

def warnInk : Color := Palette.color .dark .warning

def errorInk : Color := Palette.color .dark .error

structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Inhabited, BEq

def Box.has (b : Box) (x y : Nat) : Bool := b.x ≤ x && x < b.x + b.w && b.y ≤ y && y < b.y + b.h

/-- What a tap on a page does nothing with: the hit-test default and
the action of a piece nothing taps. -/
class Inert (α : Type) where
  inert : α

/-- A page: its content (W x the viewport's height), and its tap targets
in content rows. -/
structure PageOf (α : Type) where
  bmp : Bitmap
  taps : Array (Box × α)

def PageOf.hit {α : Type} [Inert α] (p : PageOf α) (x y : Nat) : α := Id.run do
  for (b, a) in p.taps do
    if b.has x y then return a
  return Inert.inert

/-! ## Pieces -/

/-- A line of text centred across the width. -/
def centred (f : Font) (b : Bitmap) (s : String) (y : Nat) (c : Color) (bold := false) : Bitmap :=
  let l := oneLine f b.w s
  let w := Paint.Line.width f l
  b.line f l ((b.w - min b.w w) / 2) y c bold

/-- A paragraph wrapped to width w at (x, y); its height. -/
def para (f : Font) (dm : Dim) (b : Bitmap) (s : String) (x y w : Nat) (c : Color) : Bitmap × Nat := Id.run do
  let ls := Text.layout f w s
  let mut b := b
  for i in [0:ls.size] do
    b := b.line f ls[i]! x (y + i * dm.lineH) c
  return (b, ls.size * dm.lineH)

/-- libquiet's Rows: a rounded card of rows, each an icon, a label and a
chevron, divided by lines. -/
def rows {α : Type} [BEq α] [Inert α] (f : Font) (dm : Dim) (b : Bitmap) (y : Nat) (items : Array (String × String × α)) :
    Bitmap × Array (Box × α) × Nat := Id.run do
  let x0 := dm.px 24
  let x1 := b.w - dm.px 24
  let rh := dm.px 56
  let h := items.size * rh
  let mut b := b.round x0 y x1 (y + h) (dm.px 16) (Palette.color dm.theme .edge)
  let e := max 2 (dm.px 1)
  b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 16 - e) (Palette.color dm.theme .panel)
  let mut taps := #[]
  for i in [0:items.size] do
    let (icon, label, act) := items[i]?.getD ("", "", Inert.inert)
    let ry := y + i * rh
    if i > 0 then b := b.fill (x0 + e) ry (x1 - e) (ry + max 1 (dm.px 1) / 2 + 1) (Palette.color dm.theme .edge)
    if dm.hot x0 ry (x1 - x0) rh (act != Inert.inert) then b := b.fill (x0 + e) (ry + e) (x1 - e) (ry + rh - e) (Palette.color dm.theme .selected)
    let ty := ry + (rh - f.cell) / 2
    b := b.line f (oneLine f (f.cell * 2) icon) (x0 + dm.px 16) ty (Palette.color dm.theme .fg)
    b := b.line f (oneLine f (x1 - x0 - dm.px 120) label) (x0 + dm.px 16 + f.cell + dm.px 16) ty (Palette.color dm.theme .fg)
    b := b.line f (oneLine f f.cell "›") (x1 - dm.px 16 - f.cell / 2) ty (Palette.color dm.theme .muted)
    taps := taps.push (⟨x0, ry, x1 - x0, rh⟩, act)
  return (b, taps, h)

/-- A wide button: primary (filled) or secondary (outlined). -/
def button {α : Type} [BEq α] [Inert α] (f : Font) (dm : Dim) (b : Bitmap) (label : String) (y : Nat) (filled : Bool) (act : α) :
    Bitmap × (Box × α) × Nat := Id.run do
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 48
  let mut b := b
  let hot := dm.hot x0 y (x1 - x0) h (act != Inert.inert)
  if filled then
    b := b.round x0 y x1 (y + h) (dm.px 12) (Hover.choose dm.hover ⟨x0, y, x1 - x0, h⟩ (act != Inert.inert) (Palette.color dm.theme .button) (Palette.buttonHover dm.theme))
  else
    let e := max 2 (dm.px 1)
    b := b.round x0 y x1 (y + h) (dm.px 12) (if hot then Palette.gray30 dm.theme else Palette.color dm.theme .edge)
    b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 12 - e) (if hot then Palette.gray03 dm.theme else Palette.color dm.theme .bg)
  b := centred f b label (y + (h - f.cell) / 2) (Palette.color dm.theme (if filled then .onAccent else .fg))
  return (b, (⟨x0, y, x1 - x0, h⟩, act), h)

/-- A danger button (libquiet's): red, for what cannot be undone. -/
def dangerButton {α : Type} [BEq α] [Inert α] (f : Font) (dm : Dim) (b : Bitmap) (label : String) (y : Nat) (act : α) :
    Bitmap × (Box × α) × Nat :=
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 48
  let b := (b.round x0 y x1 (y + h) (dm.px 12) (if dm.hot x0 y (x1 - x0) h (act != Inert.inert) then 0xba272b else Palette.color dm.theme .danger))
  (centred f b label (y + (h - f.cell) / 2) (Palette.color dm.theme .onAccent), (⟨x0, y, x1 - x0, h⟩, act), h)

/-- A one-line field (the keyboard's text): its box, the text or a
placeholder, the caret, and an error edge. -/
def field {α : Type} (f : Font) (dm : Dim) (b : Bitmap) (y : Nat) (text placeholder : String) (focused : Bool)
    (bad : Bool) (act : α) : Bitmap × (Box × α) × Nat := Id.run do
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 52
  let e := max 2 (dm.px 1)
  let mut b := b.round x0 y x1 (y + h) (dm.px 10) (if bad then (Palette.color dm.theme .error) else if focused then (Palette.color dm.theme .accentInk) else (Palette.color dm.theme .edge))
  b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 10 - e) (Palette.color dm.theme .selected)
  let ty := y + (h - f.cell) / 2
  let w := x1 - x0 - dm.px 32
  -- a long (Palette.color dm.theme .link) shows its end, where the caret is
  let l := if text.isEmpty then oneLine f w placeholder else
    let full := oneLine f (10 * b.w) text
    let fw := Paint.Line.width f full
    if fw ≤ w then full else (full.filter (·.x + fw ≥ w + f.cell)).map fun g => { g with x := g.x + w - fw }
  b := b.line f l (x0 + dm.px 16) ty (if text.isEmpty then (Palette.color dm.theme .muted) else (Palette.color dm.theme .fg))
  if focused then
    let cx := x0 + dm.px 16 + (if text.isEmpty then 0 else min w (Paint.Line.width f l))
    b := b.fill cx ty (cx + e + 1) (ty + f.cell) (Palette.color dm.theme .accentInk)
  return (b, (⟨x0, y, x1 - x0, h⟩, act), h)

/-- A page's bar: a back arrow or a cross on the left, the title centred. -/
def bar (f : Font) (dm : Dim) (W insetTop : Nat) (title : String) (cross : Bool) : Bitmap := Id.run do
  let h := insetTop + dm.px 56
  let mut b := Bitmap.blank W h (solid (Palette.color dm.theme .bg) W)
  let ty := insetTop + (dm.px 56 - f.cell) / 2
  b := b.line f (oneLine f f.cell (if cross then "✕" else "←")) (dm.px 16) ty (Palette.color dm.theme .fg)
  b := centred f b title ty (Palette.color dm.theme .fg) true
  return b

/-- The bar's back target, in the bar's own rows. -/
def barBack (dm : Dim) (insetTop : Nat) : Box := ⟨0, insetTop, dm.px 64, dm.px 56⟩

/-- The heading a Stage opens with, 24 dp under the bar. -/
def heading (f : Font) (dm : Dim) (b : Bitmap) (s : String) (y : Nat) : Bitmap × Nat :=
  (centred f b s y (Palette.color dm.theme .fg) true, f.cell + dm.px 8)

def blank (W h : Nat) (theme : Theme.Value := .dark) : Bitmap :=
  Bitmap.blank W h (solid (Palette.color theme .bg) W)

/-! ## The pages -/

/-- libquiet's toast: centred, a rounded panel, a mark over one or two
lines; drawn over the list for about 3 s. -/
def toast (f : Font) (dm : Dim) (W : Nat) (text : String) : Bitmap := Id.run do
  let w := min (W - dm.px 32) (dm.px 280)
  let ls := Text.layout f (w - dm.px 32) text
  let h := dm.px 16 + f.cell + dm.px 8 + (min 2 ls.size) * dm.lineH + dm.px 16
  let mut b := Bitmap.blank w h (solid (Palette.color dm.theme .bg) w)
  b := b.round 0 0 w h (dm.px 16) (Palette.color dm.theme .edge)
  let e := max 2 (dm.px 2)
  b := b.round e e (w-e) (h-e) (dm.px 16-e) (Palette.color dm.theme .toast)
  b := centred f b "✓" (dm.px 16) (Palette.color dm.theme .online) true
  for i in [0:min 2 ls.size] do
    let lw := Paint.Line.width f ls[i]!
    b := b.line f ls[i]! ((w - min w lw) / 2) (dm.px 16 + f.cell + dm.px 8 + i * dm.lineH) (Palette.color dm.theme .fg)
  return b

/-- A square avatar for a community: its initial on a colour from its id. -/
def avatarColor (id8 : String) : Color := Palette.avatar id8

/-! ## Home -/

def band : Color := Palette.color .dark .accent

def badgeRed : Color := Palette.color .dark .badge

/-- A red count badge (libquiet's), its right edge at x. -/
def badge (f : Font) (dm : Dim) (b : Bitmap) (n : Nat) (xr y : Nat) : Bitmap :=
  let l := oneLine f (4 * f.cell) (if n > 99 then "99+" else toString n)
  let w := max (dm.px 24) (Paint.Line.width f l + dm.px 12)
  let h := dm.px 24
  -- Count pills are a flat fill in libquiet; the adaptive toast edge
  -- adds a conspicuous white halo on a dark list.
  let b := b.round (xr-w) y xr (y+h) (h/2) (Palette.color dm.theme .badge)
  b.line f l (xr - w + (w - Paint.Line.width f l) / 2) (y + (h - f.cell) / 2) (Palette.color dm.theme .onAccent)

end Pages
