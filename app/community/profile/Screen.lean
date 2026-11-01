import engine.renderer.Page

/-!
A member's profile, and the page for two members whose names look alike.
-/

namespace Pages
open Paint Text Font Row

/-- A member's profile: their initial and name; "(you)" on yours;
"Removed from community" on a removed member's; and Remove from
community (danger) when it is offered (Remove.offered). -/
def profile {α : Type} [BEq α] [Inert α] (onYou : α) (onRemove : α) (f : Font) (dm : Dim) (W h : Nat) (name : String) (isMe removed canRemove : Bool) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let d := dm.px 72
  let y0 := dm.px 32
  b := b.round ((W - d) / 2) y0 ((W + d) / 2) (y0 + d) (dm.px 8) (avatarColor name)
  b := centred f b (String.ofList [(name.toList.headD '?').toUpper]) (y0 + (d - f.cell) / 2) (Palette.color dm.theme .onAccent) true
  let mut y := y0 + d + dm.px 20
  b := centred f b name y (Palette.color dm.theme .fg) true
  y := y + f.cell + dm.px 8
  if isMe then b := centred f b "(you)" y (Palette.color dm.theme .muted)
  if removed then b := centred f b "Removed from community" y (Palette.color dm.theme .muted)
  y := y + f.cell + dm.px 32
  let mut taps := #[]
  if isMe then
    let (b1, ts, _) := rows f dm b y #[("◐", "You", onYou)]
    b := b1
    taps := ts
  if canRemove then
    let (b1, t, _) := dangerButton f dm b "Remove from community" y onRemove
    b := b1
    taps := taps.push t
  return ⟨b, taps⟩

/-- Quiet's duplicate-name warning, opened from a "Duplicate" label:
what it means, and the label itself. -/
def duplicate {α : Type} [BEq α] [Inert α] (f : Font) (dm : Dim) (W h : Nat) : PageOf α := Id.run do
  let mut b := blank W h
  let mut y := dm.px 24
  let (b1, hh) := heading f dm b "Multiple users with same name" y
  y := y + hh + dm.px 12
  let (b2, ph) := para f dm b1
    "Two members are using names that look the same. This should be rare, and could mean someone is impersonating another member. Both are marked:"
    (dm.px 24) y (W - dm.px 48) dim
  b := b2
  y := y + ph + dm.px 16
  let (bx, l) := Row.twinPill f dm 0
  let x := (W - min W bx.w) / 2
  b := b.round x y (x + bx.w) (y + bx.h) (dm.px 8) Row.twinBg
  b := b.line f l (x + dm.px 6) (y + (dm.topPad - bx.y)) nameInk
  return ⟨b, #[]⟩

end Pages
