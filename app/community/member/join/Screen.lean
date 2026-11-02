import engine.renderer.Page

/-!
Joining's pages: how to join, the invite link, pasting it, scanning
its QR code, choosing a name, and agreeing to join.
-/

namespace Pages
open Paint Text Font Row

/-- Join community: invite link or QR code. -/
def joinChoice {α : Type} [BEq α] [Inert α] (onInviteLink : α) (onQrCode : α) (f : Font) (dm : Dim) (W h : Nat) (status : Option String) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Join community" (dm.px 24)
  let mut y := dm.px 24 + hh + dm.px 24
  b := b1
  if let some st := status then
    let (b2, ph) := para f dm b st (dm.px 24) y (W - dm.px 48) (Palette.color dm.theme .error)
    b := b2; y := y + ph + dm.px 12
  let (b3, taps, _) := rows f dm b y #[("⛓", "Join with invite link", onInviteLink), ("▦", "Join with QR code", onQrCode)]
  return ⟨b3, taps⟩

/-- Link devices, on a device not yet in the community (libquiet
`LinkDevices.svelte`'s receive side): scan the other device's code, or
paste its link. -/
def linkChoice {α : Type} [BEq α] [Inert α] (onQrCode : α) (onPasteLink : α) (f : Font) (dm : Dim) (W h : Nat) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Link devices" (dm.px 24)
  let (b2, ph) := para f dm b1 "Go to “Link devices” on the other device and display the QR code. Scan it to link devices."
    (dm.px 24) (dm.px 24 + hh + dm.px 16) (W - dm.px 48) (Palette.color dm.theme .fg)
  b := b2
  let (b3, taps, _) := rows f dm b (dm.px 24 + hh + dm.px 16 + ph + dm.px 24) #[("▦", "Scan QR code", onQrCode), ("⛓", "Paste link", onPasteLink)]
  return ⟨b3, taps⟩

/-- Join with invite link: the explainer, and the sentence-button that
opens the paste field. -/
def openInvite {α : Type} [BEq α] [Inert α] (onPasteLink : α) (f : Font) (dm : Dim) (W h : Nat) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Join with invite link" (dm.px 24)
  let (b2, ph) := para f dm b1 "Open an invite link from a community admin. (If you just installed Quiet, open the invite again!)"
    (dm.px 24) (dm.px 24 + hh + dm.px 16) (W - dm.px 48) (Palette.color dm.theme .fg)
  let y := dm.px 24 + hh + dm.px 16 + ph + dm.px 24
  let l := oneLine f W "Paste a link"
  let w := Paint.Line.width f l
  b := b2.line f l ((W - w) / 2) y (Palette.color dm.theme .link)
  b := if dm.hot ((W - w) / 2) y w f.cell then
    b.fill ((W - w) / 2) (y + f.cell + dm.px 2) ((W + w) / 2) (y + f.cell + dm.px 3) (Palette.color dm.theme .link) else b
  return ⟨b, #[(⟨(W - w) / 2, y, w, f.cell⟩, onPasteLink)]⟩

/-- Paste a link to join: one field, one button; a refusal under it.
With `device`, Link devices' (libquiet `Linking.svelte`). -/
def paste {α : Type} [BEq α] [Inert α] (onContinue onField : α) (f : Font) (dm : Dim) (W h : Nat) (text : String) (focused : Bool) (refusal : Option String)
    (device : Bool := false) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b (if device then "Paste link" else "Paste a link to join") (dm.px 24)
  let fy := dm.px 24 + hh + dm.px 40
  let (b2, ft, fh) := field f dm b1 fy text (if device then "Device link from your other device" else "Invite link") focused refusal.isSome onField
  b := b2
  let mut y := fy + fh + dm.px 8
  if let some r := refusal then
    let (b3, ph) := para f dm b (Cue.caption dm.theme .error ++ ": " ++ r) (dm.px 16) y (W - dm.px 32) (Palette.color dm.theme .error)
    b := b3; y := y + ph
  let (b4, bt, _) := button f dm b "Continue" (y + dm.px 16) (!text.trimAscii.isEmpty) onContinue
  return ⟨b4, #[ft, bt]⟩

/-- Where Join with QR code shows the camera: a square, in page rows. -/
def scanBox (dm : Dim) (W h : Nat) : Box :=
  let s := min (W - dm.px 96) (h / 2)
  ⟨(W - s) / 2, dm.px 24, s, s⟩

/-- Join with QR code: the camera's square (its frames, or why there are
none), the instruction, and the way to paste instead. -/
def scan {α : Type} [BEq α] [Inert α] (onPasteLink : α) (f : Font) (dm : Dim) (W h : Nat) (camera : Option Bitmap) (note : String)
    (device : Bool := false) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let ⟨x, y, s, _⟩ := scanBox dm W h
  match camera with
  | some img => b := b.image img x y (dm.px 12)
  | none =>
    b := b.round x y (x + s) (y + s) (dm.px 12) (Palette.color dm.theme .scrim)
    b := centred f b note (y + (s - f.cell) / 2) (Palette.color dm.theme .fg)
  let (b2, ph) := para f dm b "Point the camera at the QR code on the other device." (dm.px 24) (y + s + dm.px 24) (W - dm.px 48) (Palette.color dm.theme .fg)
  let ly := y + s + dm.px 24 + ph + dm.px 24
  let l := oneLine f W (if device then "Paste link instead" else "Paste a link to join")
  let w := Paint.Line.width f l
  b := b2.line f l ((W - w) / 2) ly (Palette.color dm.theme .link)
  b := if dm.hot ((W - w) / 2) ly w f.cell then
    b.fill ((W - w) / 2) (ly + f.cell + dm.px 2) ((W + w) / 2) (ly + f.cell + dm.px 3) (Palette.color dm.theme .link) else b
  return ⟨b, #[(⟨(W - w) / 2, ly, w, f.cell⟩, onPasteLink)]⟩

/-- Choose a name: what others will see, before Agree & join. -/
def chooseName {α : Type} [BEq α] [Inert α] (onContinue onField : α) (f : Font) (dm : Dim) (W h : Nat) (name : String) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Choose a name" (dm.px 24)
  let (b2, ph) := para f dm b1 "This is how you'll appear to others in this community." (dm.px 24) (dm.px 24 + hh + dm.px 8) (W - dm.px 48) (Palette.color dm.theme .muted)
  let fy := dm.px 24 + hh + dm.px 8 + ph + dm.px 24
  let (b3, ft, fh) := field f dm b2 fy name "Your name" true false onField
  let (b4, bt, _) := button f dm b3 "Continue" (fy + fh + dm.px 24) (!name.trimAscii.isEmpty) onContinue
  b := b4
  return ⟨b, #[ft, bt]⟩

/-- Agree & join: what joining means, and the one button. -/
def agree {α : Type} [BEq α] [Inert α] (onAgree : α) (f : Font) (dm : Dim) (W h : Nat) (community : String)
    (device : Bool := false) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  -- a device link's (libquiet `DeviceLinkConfirm.svelte`)
  let text := if device then "This device will join the community as another device of the person who made this link. Continue only if you trust the person who shared the link."
    else s!"Joining {community} shares your device's public key and what you post with its members, and gives them your history from here on. This community may include an always-on cloud server, which cannot read what is said here but sees who is in the community and when they post."
  let (b1, ph) := para f dm b text (dm.px 16) (dm.px 24) (W - dm.px 32) (Palette.color dm.theme .fg)
  let (b2, bt, _) := button f dm b1 (if device then "Link device" else "Agree & Join") (dm.px 24 + ph + dm.px 24) true onAgree
  b := b2
  return ⟨b, #[bt]⟩

end Pages
