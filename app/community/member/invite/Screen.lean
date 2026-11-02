import engine.renderer.Page

/-!
Inviting: the invite link to share, as text and as a QR code.
-/

namespace Pages
open Paint Text Font Row

/-- The QR code's square on Add members. -/
def qrSide (dm : Dim) (W h : Nat) : Nat := min (W - dm.px 128) (h / 3)

/-- Add members: the QR code (or its square while there is none), the
share button, the link with Copy, the caution, what happens next. With
`device`, Link devices' share side (libquiet `DeviceCode.svelte`): the
same for a device link, and this user's devices under it. -/
def invite {α : Type} [BEq α] [Inert α] (onShare : α) (onCopy : α) (f : Font) (dm : Dim) (W h : Nat) (qr : Option Bitmap) (linkText : String)
    (device : Bool := false) (devices : Array String := #[]) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let s := qrSide dm W h
  let x := (W - s) / 2
  let y := dm.px 24
  b := b.round (x - dm.px 16) (y - dm.px 16) (x + s + dm.px 16) (y + s + dm.px 16) (dm.px 12) (Palette.color dm.theme .edge)
  b := b.round (x - dm.px 15) (y - dm.px 15) (x + s + dm.px 15) (y + s + dm.px 15) (dm.px 12) (Palette.color dm.theme .bg)
  -- white under the code (its quiet zone is white too), whole pixels
  b := b.round x y (x + s) (y + s) (dm.px 8) (Palette.color dm.theme .white)
  if let some q := qr then b := b.image q (x + (s - q.w) / 2) (y + (s - q.h) / 2) 0
  let mut yy := y + s + dm.px 32
  b := centred f b (if device then "Scan this from “Link devices” on your new device." else "Scan with the Quiet app to ask to join.") yy (Palette.color dm.theme .muted)
  yy := yy + f.cell + dm.px 24
  let (b1, st, sh) := button f dm b (if device then "Share device link" else "Share invite link") yy true onShare
  b := b1
  yy := yy + sh + dm.px 16
  -- the (Palette.color dm.theme .link) and Copy
  let lx0 := dm.px 16
  let lx1 := W - dm.px 16
  let cw := dm.px 72
  let ls := Text.layout f (lx1 - lx0 - cw - dm.px 32) linkText
  let lh := max (dm.px 56) (ls.size * dm.lineH + dm.px 16)
  b := b.round lx0 yy lx1 (yy + lh) (dm.px 10) (Palette.color dm.theme .edge)
  b := b.round (lx0 + 2) (yy + 2) (lx1 - 2) (yy + lh - 2) (dm.px 10 - 2) (Palette.color dm.theme .bg)
  for i in [0:ls.size] do
    b := b.line f ls[i]! (lx0 + dm.px 16) (yy + dm.px 8 + i * dm.lineH) (Palette.color dm.theme .muted)
  let cx := lx1 - dm.px 8 - cw
  let cy := yy + (lh - dm.px 40) / 2
  b := b.round cx cy (cx + cw) (cy + dm.px 40) (dm.px 20) (Palette.color dm.theme .edge)
  b := b.round (cx + 2) (cy + 2) (cx + cw - 2) (cy + dm.px 40 - 2) (dm.px 20 - 2) (if dm.hot cx cy cw (dm.px 40) then Palette.gray03 dm.theme else Palette.color dm.theme .bg)
  b := centred f (Bitmap.blank cw f.cell (solid (if dm.hot cx cy cw (dm.px 40) then Palette.gray03 dm.theme else Palette.color dm.theme .bg) cw)) "Copy" 0 (Palette.color dm.theme .fg) |>.rows.foldl (fun (acc : Bitmap × Nat) row =>
    (acc.1.modify (cy + (dm.px 40 - f.cell) / 2 + acc.2) (fun r => row.copySlice 0 r (4 * cx) (4 * cw)), acc.2 + 1)) (b, 0) |>.1
  let ct : Box × α := (⟨cx, cy, cw, dm.px 40⟩, onCopy)
  yy := yy + lh + dm.px 16
  let (b2, ph) := para f dm b (if device then "Anyone holding this link or code can ask to join as one of your devices, and a link can't be cancelled once it's sent. Use it only on your own devices."
    else "Anyone holding this link or code can ask to join, and a link can't be cancelled once it's sent. Share it only with people you trust.") (dm.px 16) yy (W - dm.px 32) (Palette.color dm.theme .muted)
  b := b2
  yy := yy + ph + dm.px 24
  b := b.line f (oneLine f W "What happens next") (dm.px 16) yy (Palette.color dm.theme .muted) true
  yy := yy + dm.lineH + dm.px 8
  let steps := if device then #["1. On the new device, open Link devices from Get started, and scan this code or paste the link.",
      "2. It appears under Waiting to join as your device.", "3. Approve it there: it joins this community as you."]
    else #["1. They open the link, or scan the code, in Quiet.", "2. Their device appears under Waiting to join.",
      "3. Once a member vouches for them, they can read and post here."]
  for st in steps do
    let (b3, sh2) := para f dm b st (dm.px 16) yy (W - dm.px 32) (Palette.color dm.theme .fg)
    b := b3
    yy := yy + sh2 + dm.px 8
  if device && !devices.isEmpty then
    yy := yy + dm.px 16
    b := b.line f (oneLine f W "Linked devices") (dm.px 16) yy (Palette.color dm.theme .muted) true
    yy := yy + dm.lineH + dm.px 8
    for d in devices do
      b := b.line f (oneLine f (W - dm.px 32) d) (dm.px 16) yy (Palette.color dm.theme .fg)
      yy := yy + dm.lineH + dm.px 4
  return ⟨b, #[st, ct]⟩

end Pages
