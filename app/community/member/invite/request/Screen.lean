import engine.renderer.Page

/-!
Join requests: who asks to join, each to approve or hide.
-/

namespace Pages
open Paint Text Font Row

/-- One device asking to join. -/
structure Asking where
  device : String
  when : String
  going : Bool
  deriving Inhabited, BEq, Repr

/-- Join requests: who is waiting, each with approve and hide; or none,
and the way to add members. -/
def requests {α : Type} [BEq α] [Inert α] (onAddMembers : α) (onHide : Nat → α) (onApprove : Nat → α) (f : Font) (dm : Dim) (W h : Nat) (asking : Array Asking) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let mut taps := #[]
  if asking.isEmpty then
    b := centred f b "No one is waiting to join" (dm.px 72) (Palette.color dm.theme .fg) true
    let l := oneLine f W "Add members"
    let w := Paint.Line.width f l + dm.px 32
    let x := (W - w) / 2
    let y := dm.px 72 + f.cell + dm.px 24
    b := b.round x y (x + w) (y + dm.px 44) (dm.px 22) (Palette.color dm.theme .edge)
    b := b.round (x + 2) (y + 2) (x + w - 2) (y + dm.px 44 - 2) (dm.px 22 - 2) (Palette.color dm.theme .panel)
    b := b.line f l (x + dm.px 16) (y + (dm.px 44 - f.cell) / 2) (Palette.color dm.theme .fg)
    return ⟨b, #[(⟨x, y, w, dm.px 44⟩, onAddMembers)]⟩
  b := b.line f (oneLine f W s!"{asking.size} waiting") (dm.px 16) (dm.px 16) (Palette.color dm.theme .muted)
  let rh := dm.px 64
  for i in [0:asking.size] do
    let a := asking[i]!
    let y := dm.px 16 + f.cell + dm.px 8 + i * rh
    let d := dm.px 32
    b := b.round (dm.px 16) (y + (rh - d) / 2) (dm.px 16 + d) (y + (rh + d) / 2) (dm.px 6) (Palette.color dm.theme .edge)
    b := b.line f (oneLine f f.cell "?") (dm.px 16 + (d - f.cell / 2) / 2) (y + (rh - f.cell) / 2) (Palette.color dm.theme .fg)
    let tx := dm.px 16 + d + dm.px 12
    b := b.line f (oneLine f (W / 2) a.device) tx (y + dm.px 4) (Palette.color dm.theme .fg) true
    b := b.line f (oneLine f (W / 2) s!"New person · {a.when}") tx (y + dm.px 4 + f.cell) (Palette.color dm.theme .muted)
    -- approve (a check) and hide (a cross), right-aligned
    let k := dm.px 40
    let ax := W - dm.px 16 - k
    let hx := ax - dm.px 8 - k
    let ky := y + (rh - k) / 2
    b := b.round hx ky (hx + k) (ky + k) (k / 2) (if dm.hot hx ky k k then Palette.color dm.theme .selected else Palette.color dm.theme .edge)
    b := b.line f (oneLine f f.cell "✕") (hx + (k - f.cell / 2) / 2) (ky + (k - f.cell) / 2) (Palette.color dm.theme .fg)
    b := b.round ax ky (ax + k) (ky + k) (k / 2) (if a.going then (Palette.color dm.theme .edge) else if dm.hot ax ky k k then Palette.buttonHover dm.theme else (Palette.color dm.theme .button))
    b := b.line f (oneLine f f.cell (if a.going then "…" else "✓")) (ax + (k - f.cell / 2) / 2) (ky + (k - f.cell) / 2) (Palette.color dm.theme .onAccent)
    taps := taps.push (⟨hx, ky, k, k⟩, onHide i) |>.push (⟨ax, ky, k, k⟩, onApprove i)
  return ⟨b, taps⟩

end Pages
