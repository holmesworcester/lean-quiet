/-
The app's pages besides a conversation, in the layout and spirit of
libquiet's phone screens (its Stage, Rows and sheets): Get started,
Create a community, Join community, Join with invite link, Paste a link,
Join with QR code, Agree & join, Waiting to join, Join requests, Add
members, and the community switcher.

A page is a pure picture of the screen's content (drawn into the list
layer, which does not scroll on a page) plus its bar (drawn into the
header layer), and the boxes a tap can land on, each with what it does.
The painter and the taps read the same boxes.
-/
import engine.renderer.Row
import engine.renderer.Overlay
import engine.renderer.Label

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

/-- What a tap on a page does. -/
inductive Act where
  | back
  | you | appearance | theme (setting : Theme.Setting)
  | communitySettings | channelSettings | stub (title : String)
  | joinCommunity
  | createCommunity
  | inviteLink
  | qrCode
  | pasteLink
  | field
  | continue_
  | agree
  | addMembers
  | share
  | copy
  | approve (i : Nat)
  | hide (i : Nat)
  | switchTo (i : Nat)
  | addCommunity
  | requests
  | openChannel (i : Nat)
  | stopWaiting
  /-- A person on home (people list row i): their profile. -/
  | person (i : Nat)
  | removeStart
  | removeYes
  | removeCancel
  | copyLabel | labelNext | labelPrev
  | none
  deriving BEq, Inhabited, Repr

/-- The source label behind each compact navigation row. -/
def fullLabel (a : Act) (communities people : Array String) : Option String :=
  match a with
  | .switchTo i => communities[i]?
  | .person i => people[i]?
  | .openChannel _ => some "general"
  | .requests => some "Waiting to join"
  | .joinCommunity => some "Join a community"
  | .createCommunity => some "Create a community"
  | .inviteLink => some "Join with invite link"
  | .qrCode => some "Join with QR code"
  | _ => none

structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Inhabited, BEq

def Box.has (b : Box) (x y : Nat) : Bool := b.x ≤ x && x < b.x + b.w && b.y ≤ y && y < b.y + b.h

/-- A page: its content (W x the viewport's height), and its tap targets
in content rows. -/
structure Page where
  bmp : Bitmap
  taps : Array (Box × Act)

def Page.hit (p : Page) (x y : Nat) : Act := Id.run do
  for (b, a) in p.taps do
    if b.has x y then return a
  return .none

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
def rows (f : Font) (dm : Dim) (b : Bitmap) (y : Nat) (items : Array (String × String × Act)) :
    Bitmap × Array (Box × Act) × Nat := Id.run do
  let x0 := dm.px 24
  let x1 := b.w - dm.px 24
  let rh := dm.px 56
  let h := items.size * rh
  let mut b := b.round x0 y x1 (y + h) (dm.px 16) (Palette.color dm.theme .edge)
  let e := max 2 (dm.px 1)
  b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 16 - e) (Palette.color dm.theme .panel)
  let mut taps := #[]
  for i in [0:items.size] do
    let (icon, label, act) := items[i]!
    let ry := y + i * rh
    if i > 0 then b := b.fill (x0 + e) ry (x1 - e) (ry + max 1 (dm.px 1) / 2 + 1) (Palette.color dm.theme .edge)
    if dm.hot x0 ry (x1 - x0) rh (act != .none) then b := b.fill (x0 + e) (ry + e) (x1 - e) (ry + rh - e) (Palette.color dm.theme .selected)
    let ty := ry + (rh - f.cell) / 2
    b := b.line f (oneLine f (f.cell * 2) icon) (x0 + dm.px 16) ty (Palette.color dm.theme .fg)
    b := b.line f (oneLine f (x1 - x0 - dm.px 120) label) (x0 + dm.px 16 + f.cell + dm.px 16) ty (Palette.color dm.theme .fg)
    b := b.line f (oneLine f f.cell "›") (x1 - dm.px 16 - f.cell / 2) ty (Palette.color dm.theme .muted)
    taps := taps.push (⟨x0, ry, x1 - x0, rh⟩, act)
  return (b, taps, h)

/-- A wide button: primary (filled) or secondary (outlined). -/
def button (f : Font) (dm : Dim) (b : Bitmap) (label : String) (y : Nat) (filled : Bool) (act : Act) :
    Bitmap × (Box × Act) × Nat := Id.run do
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 48
  let mut b := b
  let hot := dm.hot x0 y (x1 - x0) h (act != .none)
  if filled then
    b := b.round x0 y x1 (y + h) (dm.px 12) (Hover.choose dm.hover ⟨x0, y, x1 - x0, h⟩ (act != .none) (Palette.color dm.theme .button) (Palette.buttonHover dm.theme))
  else
    let e := max 2 (dm.px 1)
    b := b.round x0 y x1 (y + h) (dm.px 12) (if hot then Palette.gray30 dm.theme else Palette.color dm.theme .edge)
    b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 12 - e) (if hot then Palette.gray03 dm.theme else Palette.color dm.theme .bg)
  b := centred f b label (y + (h - f.cell) / 2) (Palette.color dm.theme (if filled then .onAccent else .fg))
  return (b, (⟨x0, y, x1 - x0, h⟩, act), h)

/-- A danger button (libquiet's): red, for what cannot be undone. -/
def dangerButton (f : Font) (dm : Dim) (b : Bitmap) (label : String) (y : Nat) (act : Act) :
    Bitmap × (Box × Act) × Nat :=
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 48
  let b := (b.round x0 y x1 (y + h) (dm.px 12) (if dm.hot x0 y (x1 - x0) h (act != .none) then 0xba272b else Palette.color dm.theme .danger))
  (centred f b label (y + (h - f.cell) / 2) (Palette.color dm.theme .onAccent), (⟨x0, y, x1 - x0, h⟩, act), h)

/-- A one-line field (the keyboard's text): its box, the text or a
placeholder, the caret, and an error edge. -/
def field (f : Font) (dm : Dim) (b : Bitmap) (y : Nat) (text placeholder : String) (focused : Bool)
    (bad : Bool) : Bitmap × (Box × Act) × Nat := Id.run do
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
  return (b, (⟨x0, y, x1 - x0, h⟩, .field), h)

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

/-- Get started: the wordmark, then join or create. (Device linking is
left out for now.) -/
def getStarted (f : Font) (dm : Dim) (W h : Nat) : Page := Id.run do
  let mut b := blank W h dm.theme
  let ly := dm.px 72
  let d := dm.px 64
  let lx := (W - d - dm.px 16 - 5 * f.cell / 2) / 2
  b := b.round lx ly (lx + d) (ly + d) (d / 2) (Palette.color dm.theme .accentInk)
  b := b.line f (oneLine f f.cell "Q") (lx + (d - f.cell / 2) / 2) (ly + (d - f.cell) / 2) (Palette.color dm.theme .bg) true
  b := b.line f (oneLine f (W / 2) "Quiet") (lx + d + dm.px 16) (ly + (d - f.cell) / 2) (Palette.color dm.theme .accentInk) true
  let (b1, hh) := heading f dm b "Let’s get started…" (ly + d + dm.px 32)
  b := b1
  let y := ly + d + dm.px 32 + hh + dm.px 16
  let (b2, taps, rh) := rows f dm b y #[("+", "Join a community", .joinCommunity), ("✚", "Create a new community", .createCommunity)]
  b := b2
  let (b3, _) := para f dm b "⚠ Quiet is in beta and shouldn't be used for activities requiring security." (dm.px 24) (y + rh + dm.px 12) (W - dm.px 48) (Palette.color dm.theme .muted)
  return ⟨b3, taps⟩

/-- Create a community: a heading, the name field, Continue. -/
def create (f : Font) (dm : Dim) (W h : Nat) (name : String) (focused : Bool) : Page := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Create a community" (dm.px 24)
  let fy := dm.px 24 + hh + dm.px 40
  let (b2, ft, fh) := field f dm b1 fy name "Community name" focused false
  let (b3, bt, _) := button f dm b2 "Continue" (fy + fh + dm.px 24) (!name.trimAscii.isEmpty) .continue_
  b := b3
  return ⟨b, #[ft, bt]⟩

/-- Join community: invite link or QR code. -/
def joinChoice (f : Font) (dm : Dim) (W h : Nat) (status : Option String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Join community" (dm.px 24)
  let mut y := dm.px 24 + hh + dm.px 24
  b := b1
  if let some st := status then
    let (b2, ph) := para f dm b st (dm.px 24) y (W - dm.px 48) (Palette.color dm.theme .error)
    b := b2; y := y + ph + dm.px 12
  let (b3, taps, _) := rows f dm b y #[("⛓", "Join with invite link", .inviteLink), ("▦", "Join with QR code", .qrCode)]
  return ⟨b3, taps⟩

/-- Join with invite link: the explainer, and the sentence-button that
opens the paste field. -/
def openInvite (f : Font) (dm : Dim) (W h : Nat) : Page := Id.run do
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
  return ⟨b, #[(⟨(W - w) / 2, y, w, f.cell⟩, .pasteLink)]⟩

/-- Paste a link to join: one field, one button; a refusal under it. -/
def paste (f : Font) (dm : Dim) (W h : Nat) (text : String) (focused : Bool) (refusal : Option String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Paste a link to join" (dm.px 24)
  let fy := dm.px 24 + hh + dm.px 40
  let (b2, ft, fh) := field f dm b1 fy text "quiet://join/…" focused refusal.isSome
  b := b2
  let mut y := fy + fh + dm.px 8
  if let some r := refusal then
    let (b3, ph) := para f dm b (Cue.caption dm.theme .error ++ ": " ++ r) (dm.px 16) y (W - dm.px 32) (Palette.color dm.theme .error)
    b := b3; y := y + ph
  let (b4, bt, _) := button f dm b "Continue" (y + dm.px 16) (!text.trimAscii.isEmpty) .continue_
  return ⟨b4, #[ft, bt]⟩

/-- Where Join with QR code shows the camera: a square, in page rows. -/
def scanBox (dm : Dim) (W h : Nat) : Box :=
  let s := min (W - dm.px 96) (h / 2)
  ⟨(W - s) / 2, dm.px 24, s, s⟩

/-- Join with QR code: the camera's square (its frames, or why there are
none), the instruction, and the way to paste instead. -/
def scan (f : Font) (dm : Dim) (W h : Nat) (camera : Option Bitmap) (note : String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let ⟨x, y, s, _⟩ := scanBox dm W h
  match camera with
  | some img => b := b.image img x y (dm.px 12)
  | none =>
    b := b.round x y (x + s) (y + s) (dm.px 12) (Palette.color dm.theme .scrim)
    b := centred f b note (y + (s - f.cell) / 2) (Palette.color dm.theme .fg)
  let (b2, ph) := para f dm b "Point the camera at the QR code on the other device." (dm.px 24) (y + s + dm.px 24) (W - dm.px 48) (Palette.color dm.theme .fg)
  let ly := y + s + dm.px 24 + ph + dm.px 24
  let l := oneLine f W "Paste a link to join"
  let w := Paint.Line.width f l
  b := b2.line f l ((W - w) / 2) ly (Palette.color dm.theme .link)
  b := if dm.hot ((W - w) / 2) ly w f.cell then
    b.fill ((W - w) / 2) (ly + f.cell + dm.px 2) ((W + w) / 2) (ly + f.cell + dm.px 3) (Palette.color dm.theme .link) else b
  return ⟨b, #[(⟨(W - w) / 2, ly, w, f.cell⟩, .pasteLink)]⟩

/-- Choose a name: what others will see, before Agree & join. -/
def chooseName (f : Font) (dm : Dim) (W h : Nat) (name : String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Choose a name" (dm.px 24)
  let (b2, ph) := para f dm b1 "This is how you'll appear to others in this community." (dm.px 24) (dm.px 24 + hh + dm.px 8) (W - dm.px 48) (Palette.color dm.theme .muted)
  let fy := dm.px 24 + hh + dm.px 8 + ph + dm.px 24
  let (b3, ft, fh) := field f dm b2 fy name "Your name" true false
  let (b4, bt, _) := button f dm b3 "Continue" (fy + fh + dm.px 24) (!name.trimAscii.isEmpty) .continue_
  b := b4
  return ⟨b, #[ft, bt]⟩

/-- Agree & join: what joining means, and the one button. -/
def agree (f : Font) (dm : Dim) (W h : Nat) (community : String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let text := s!"Joining {community} shares your device's public key and what you post with its members, and gives them your history from here on. This community may include an always-on cloud server, which cannot read what is said here but sees who is in the community and when they post."
  let (b1, ph) := para f dm b text (dm.px 16) (dm.px 24) (W - dm.px 32) (Palette.color dm.theme .fg)
  let (b2, bt, _) := button f dm b1 "Agree & Join" (dm.px 24 + ph + dm.px 24) true .agree
  b := b2
  return ⟨b, #[bt]⟩

/-- One step of the waiting card's rail: done, now, or next. -/
inductive Beat where | done | now | next
  deriving BEq, Inhabited

/-- Waiting to be let in: the mark, the title and lead, and one card per
wait: the community's short id (a link carries no name), the rail, and
Stop waiting; then the footer. -/
def waiting (f : Font) (dm : Dim) (W h : Nat) (id8 : String) (beats : Array (String × String × Beat))
    (doing : Array String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let d := dm.px 28
  let y0 := dm.px 48
  b := b.round ((W - d) / 2) y0 ((W + d) / 2) (y0 + d) (d / 2) (Palette.color dm.theme .accentInk)
  b := b.line f (oneLine f f.cell "Q") ((W - f.cell / 2) / 2) (y0 + (d - f.cell) / 2) (Palette.color dm.theme .bg) true
  let mut y := y0 + d + dm.px 24
  b := centred f b "Waiting to be let in" y (Palette.color dm.theme .fg) true
  y := y + f.cell + dm.px 12
  b := centred f b "Someone already inside has to let you in." y (Palette.color dm.theme .muted)
  y := y + f.cell + dm.px 24
  -- the (Palette.color dm.theme .panel)
  let x0 := dm.px 24
  let x1 := W - dm.px 24
  let cy := y
  let headH := dm.px 64
  let mut ry := cy + headH + dm.px 16
  let mut rows : Array (Nat × String × String × Beat × Nat) := #[]
  let tw := x1 - x0 - dm.px 72
  for (t, sub, beat) in beats do
    let ts := Text.layout f tw t
    let ls := Text.layout f tw sub
    rows := rows.push (ry, t, sub, beat, ts.size)
    ry := ry + ts.size * dm.lineH + dm.px 4 + ls.size * dm.lineH + dm.px 16
  let doingY := ry
  ry := ry + doing.size * dm.lineH + (if doing.isEmpty then 0 else dm.px 12)
  let stopY := ry
  let cardEnd := stopY + dm.px 52
  b := b.round x0 cy x1 cardEnd (dm.px 12) (Palette.color dm.theme .edge)
  b := b.round (x0 + 2) (cy + 2) (x1 - 2) (cardEnd - 2) (dm.px 12 - 2) (Palette.color dm.theme .panel)
  -- head: the avatar of the id, the id, the caption
  let av := dm.px 36
  b := b.round (x0 + dm.px 16) (cy + (headH - av) / 2) (x0 + dm.px 16 + av) (cy + (headH + av) / 2) (dm.px 6) (Palette.color dm.theme .avatar)
  b := b.line f (oneLine f f.cell (String.ofList (id8.toList.take 2))) (x0 + dm.px 16 + (av - f.cell) / 2) (cy + (headH - f.cell) / 2) (Palette.color dm.theme .fg)
  let tx := x0 + dm.px 16 + av + dm.px 12
  b := b.line f (oneLine f (x1 - tx) s!"<{id8}>") tx (cy + dm.px 8) (Palette.color dm.theme .fg)
  b := b.line f (oneLine f (x1 - tx - dm.px 8) "Its name arrives with the first sync") tx (cy + dm.px 8 + f.cell) (Palette.color dm.theme .muted)
  b := b.fill (x0 + 2) (cy + headH) (x1 - 2) (cy + headH + 2) (Palette.color dm.theme .edge)
  -- the rail
  let mx := x0 + dm.px 24
  let mr := dm.px 9
  for i in [0:rows.size] do
    let (by0, t, sub, beat, tl) := rows[i]!
    let mcy := by0 + f.cell / 2
    if i + 1 < rows.size then
      b := b.fill (mx + mr - 1) (mcy + mr) (mx + mr + 1) (rows[i+1]!.1 + f.cell / 2 - mr) (Palette.color dm.theme .edge)
    match beat with
    | .done =>
      b := b.round mx (mcy - mr) (mx + 2 * mr) (mcy + mr) mr (Palette.color dm.theme .accentInk)
      b := b.line f (oneLine f f.cell "✓") (mx + mr - f.cell / 4) (mcy - f.cell / 2) (Palette.color dm.theme .onAccent)
    | .now =>
      b := b.round mx (mcy - mr) (mx + 2 * mr) (mcy + mr) mr (Palette.color dm.theme .accentInk)
      b := b.round (mx + 3) (mcy - mr + 3) (mx + 2 * mr - 3) (mcy + mr - 3) (mr - 3) (Palette.color dm.theme .panel)
      b := b.round (mx + mr - 4) (mcy - 4) (mx + mr + 4) (mcy + 4) 4 (Palette.color dm.theme .accentInk)
    | .next =>
      b := b.round mx (mcy - mr) (mx + 2 * mr) (mcy + mr) mr (Palette.color dm.theme .edge)
      b := b.round (mx + 3) (mcy - mr + 3) (mx + 2 * mr - 3) (mcy + mr - 3) (mr - 3) (Palette.color dm.theme .panel)
    let rx := mx + 2 * mr + dm.px 16
    let ts := Text.layout f (x1 - rx - dm.px 16) t
    for k in [0:ts.size] do
      b := b.line f ts[k]! rx (by0 + k * dm.lineH) (if beat == .now then (Palette.color dm.theme .accentInk) else if beat == .done then (Palette.color dm.theme .fg) else (Palette.color dm.theme .muted)) (beat != .next)
    let (b2, _) := para f dm b sub rx (by0 + tl * dm.lineH + dm.px 4) (x1 - rx - dm.px 16) (Palette.color dm.theme .muted)
    b := b2
  for i in [0:doing.size] do
    b := b.line f (oneLine f (x1 - x0 - dm.px 32) doing[i]!) (x0 + dm.px 16) (doingY + i * dm.lineH) (Palette.color dm.theme .muted)
  b := b.fill (x0 + 2) stopY (x1 - 2) (stopY + 2) (Palette.color dm.theme .edge)
  if dm.hot x0 stopY (x1 - x0) (dm.px 52) then b := b.fill (x0 + 2) (stopY + 2) (x1 - 2) (stopY + dm.px 52 - 2) (Palette.color dm.theme .selected)
  b := centred f b "Stop waiting" (stopY + (dm.px 52 - f.cell) / 2) (Palette.color dm.theme .muted)
  let fy := cardEnd + dm.px 24
  let (b3, _) := para f dm b "You can close Quiet. This picks up where it left off." (dm.px 24) fy (W - dm.px 48) (Palette.color dm.theme .muted)
  return ⟨b3, #[(⟨x0, stopY, x1 - x0, dm.px 52⟩, .stopWaiting)]⟩

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

/-- One device asking to join. -/
structure Asking where
  device : String
  when : String
  going : Bool
  deriving Inhabited, BEq, Repr

/-- Join requests: who is waiting, each with approve and hide; or none,
and the way to add members. -/
def requests (f : Font) (dm : Dim) (W h : Nat) (asking : Array Asking) : Page := Id.run do
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
    return ⟨b, #[(⟨x, y, w, dm.px 44⟩, .addMembers)]⟩
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
    taps := taps.push (⟨hx, ky, k, k⟩, .hide i) |>.push (⟨ax, ky, k, k⟩, .approve i)
  return ⟨b, taps⟩

/-- The QR code's square on Add members. -/
def qrSide (dm : Dim) (W h : Nat) : Nat := min (W - dm.px 128) (h / 3)

/-- Add members: the QR code (or its square while there is none), the
share button, the link with Copy, the caution, what happens next. -/
def invite (f : Font) (dm : Dim) (W h : Nat) (qr : Option Bitmap) (linkText : String) : Page := Id.run do
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
  b := centred f b "Scan with the Quiet app to ask to join." yy (Palette.color dm.theme .muted)
  yy := yy + f.cell + dm.px 24
  let (b1, st, sh) := button f dm b "Share invite link" yy true .share
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
  let ct : Box × Act := (⟨cx, cy, cw, dm.px 40⟩, .copy)
  yy := yy + lh + dm.px 16
  let (b2, ph) := para f dm b "Anyone holding this link or code can ask to join, and a link can't be cancelled once it's sent. Share it only with people you trust." (dm.px 16) yy (W - dm.px 32) (Palette.color dm.theme .muted)
  b := b2
  yy := yy + ph + dm.px 24
  b := b.line f (oneLine f W "What happens next") (dm.px 16) yy (Palette.color dm.theme .muted) true
  yy := yy + dm.lineH + dm.px 8
  let steps := #["1. They open the link, or scan the code, in Quiet.", "2. Their device appears under Waiting to join.",
    "3. Once a member vouches for them, they can read and post here."]
  for st in steps do
    let (b3, sh2) := para f dm b st (dm.px 16) yy (W - dm.px 32) (Palette.color dm.theme .fg)
    b := b3
    yy := yy + sh2 + dm.px 8
  return ⟨b, #[st, ct]⟩

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
  let b := Overlay.badge dm.theme b (xr-w) y w h (h/2) (max 2 (dm.px 2))
  b.line f l (xr - w + (w - Paint.Line.width f l) / 2) (y + (h - f.cell) / 2) (Palette.color dm.theme .onAccent)

/-- The home band (the header layer): the community's avatar and name,
with the caret that opens the switcher, and my avatar on the right. -/
def homeBand (f : Font) (dm : Dim) (W insetTop : Nat) (name id me : String) (ownId : String := "") : Bitmap := Id.run do
  let px := dm.px
  let font := f.atSize (px 16)
  let h := insetTop + px 64
  let mut b := Bitmap.blank W h (solid (Palette.color dm.theme .accent) W)
  for (text, identity, x) in [(name, id, px 16), (me, ownId, W - px 44)] do
    b := b.round x (insetTop + px 18) (x + px 28) (insetTop + px 46) (px 3) (Palette.avatar identity)
    let l := oneLine font (px 28) (String.ofList [(text.toList.headD '?').toUpper])
    b := b.line font l (x + (px 28 - Paint.Line.width font l) / 2) (insetTop + px 23) 0xffffff
  let title := oneLine font (W - px 124) name
  b := b.line font title (px 52) (insetTop + px 23) 0xffffff
  b := b.icon f "caret" (px 58 + Paint.Line.width font title) (insetTop + px 27) (px 12) 0xffffff
  b := b.round (W - px 25) (insetTop + px 39) (W - px 11) (insetTop + px 53) (px 7) (Palette.color dm.theme .accent)
  b := b.round (W - px 23) (insetTop + px 41) (W - px 13) (insetTop + px 51) (px 5) 0xebb449
  b := b.round (W - px 21) (insetTop + px 43) (W - px 15) (insetTop + px 49) (px 3) (Palette.color dm.theme .accent)
  return b

/-- One geometry for the mobile list and its child visibility declarations. -/
def homePeopleTop (dm : Dim) (waiting channels : Nat) : Nat :=
  dm.px 16 + (if waiting > 0 then dm.px 44 + dm.px 24 else 0) +
    dm.px 36 + channels * dm.px 36 + dm.px 32 + dm.px 36

def home (f : Font) (dm : Dim) (W h : Nat) (waiting : Nat) (channels : Array String)
    (people : Array (String × Bool)) (ids : Array String := #[]) : Page := Id.run do
  let px := dm.px
  let font := f.atSize (px 14)
  let ink := Palette.color dm.theme .fg
  let muted := if dm.theme == .dark then 0xa0a0a0 else 0x767676
  let mut b := Bitmap.blank W h (solid (Palette.color dm.theme .accent) W)
  b := b.round 0 0 W (h + px 16) (px 16) (Palette.color dm.theme .panel)
  let mut taps := #[]
  let mut y := px 16
  if waiting > 0 then
    if dm.hot 0 y W (px 44) then b := b.fill 0 y W (y + px 44) (Palette.color dm.theme .selected)
    b := b.icon f "icon-people" (px 16) (y + px 12) (px 20) muted
    b := b.line font (oneLine font (W - px 120) "Waiting to join") (px 48) (y + px 14) ink
    b := badge font dm b waiting (W - px 16) (y + px 10)
    taps := taps.push (⟨0, y, W, px 44⟩, Act.requests)
    y := y + px 68
  b := b.line font (oneLine font W "Channels") (px 16) (y + px 10) ink
  b := b.icon f "add" (W - px 32) (y + px 10) (px 16) ink
  taps := taps.push (⟨W - px 48, y, px 44, px 36⟩, .stub "Create channel")
  y := y + px 36
  for i in [0:channels.size] do
    if dm.hot 0 y W (px 36) then b := b.fill 0 y W (y + px 36) (Palette.color dm.theme .selected)
    b := b.icon f "hash" (px 16) (y + px 12) (px 12) muted
    b := b.line font (oneLine font (W - px 48) channels[i]!) (px 32) (y + px 10) ink
    taps := taps.push (⟨0, y, W, px 36⟩, Act.openChannel i)
    y := y + px 36
  y := y + px 32
  b := b.line font (oneLine font W "Direct messages") (px 16) (y + px 10) ink
  b := b.icon f "add" (W - px 32) (y + px 10) (px 16) ink
  taps := taps.push (⟨W - px 48, y, px 44, px 36⟩, .stub "Direct message")
  y := homePeopleTop dm waiting channels.size
  for i in [0:people.size] do
    let (name, isMe) := people[i]!
    if y + px 40 > h then break
    if dm.hot 0 y W (px 40) then b := b.fill 0 y W (y + px 40) (Palette.color dm.theme .selected)
    b := b.round (px 16) (y + px 8) (px 40) (y + px 32) (px 3) (Palette.avatar (ids[i]?.getD name))
    let initial := oneLine font (px 24) (String.ofList [(name.toList.headD '?').toUpper])
    b := b.line font initial (px 16 + (px 24 - Paint.Line.width font initial) / 2) (y + px 12) 0xffffff
    let l := oneLine font (W - px 96) name
    b := b.line font l (px 48) (y + px 12) ink
    if isMe then b := b.line font (oneLine font W "(you)") (px 52 + Paint.Line.width font l) (y + px 12) muted
    taps := taps.push (⟨0, y, W, px 40⟩, Act.person i)
    y := y + px 40
  return ⟨b, taps⟩

/-- A member's profile: their initial and name; "(you)" on yours;
"Removed from community" on a removed member's; and Remove from
community (danger) when it is offered (Remove.offered). -/
def profile (f : Font) (dm : Dim) (W h : Nat) (name : String) (isMe removed canRemove : Bool) : Page := Id.run do
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
    let (b1, ts, _) := rows f dm b y #[("◐", "You", .you)]
    b := b1
    taps := ts
  if canRemove then
    let (b1, t, _) := dangerButton f dm b "Remove from community" y .removeStart
    b := b1
    taps := taps.push t
  return ⟨b, taps⟩

/-- Removing a member, asked twice (libquiet's): first what it does, then
that it cannot be undone; while it is written, that it is; a refusal
with its reason and Try again. Nothing is written before the second
confirmation (Remove.writes_only_after_two). -/
def removeConfirm (f : Font) (dm : Dim) (W h : Nat) (name : String) (stage : Nat) (why : String) : Page := Id.run do
  let mut b := blank W h dm.theme
  let mut y := dm.px 24
  let (title, body) := match stage with
    | 1 => (s!"Remove {name}?",
            s!"{name} will stop receiving this community's messages once their devices learn of the removal. Copies they already have are not deleted.")
    | 2 => ("This can't be undone",
            s!"{name} can only come back with a new invitation, approved again.")
    | 3 => ("Removing…", s!"Telling the community that {name} is removed.")
    | _ => ("Couldn't remove", why)
  let (b1, hh) := heading f dm b title y
  y := y + hh + dm.px 12
  let (b2, ph) := para f dm b1 body (dm.px 24) y (W - dm.px 48) (if stage == 4 then (Palette.color dm.theme .error) else (Palette.color dm.theme .muted))
  b := b2
  y := y + ph + dm.px 32
  let mut taps := #[]
  match stage with
  | 1 =>
    let (b3, t1, h1) := button f dm b "Continue" y true .removeYes
    let (b4, t2, _) := button f dm b3 "Cancel" (y + h1 + dm.px 12) false .removeCancel
    b := b4; taps := #[t1, t2]
  | 2 =>
    let (b3, t1, h1) := dangerButton f dm b s!"Remove {name}" y .removeYes
    let (b4, t2, _) := button f dm b3 "Cancel" (y + h1 + dm.px 12) false .removeCancel
    b := b4; taps := #[t1, t2]
  | 3 => pure ()
  | _ =>
    let (b3, t1, h1) := dangerButton f dm b "Try again" y .removeYes
    let (b4, t2, _) := button f dm b3 "Cancel" (y + h1 + dm.px 12) false .removeCancel
    b := b4; taps := #[t1, t2]
  return ⟨b, taps⟩

/-- Quiet's duplicate-name warning, opened from a "Duplicate" label:
what it means, and the label itself. -/
def duplicate (f : Font) (dm : Dim) (W h : Nat) : Page := Id.run do
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

/-- One community in the switcher. -/
structure Entry where
  name : String
  /-- Its id's first eight hex digits (what a pending join shows). -/
  id8 : String
  unread : Nat
  current : Bool
  waiting : Bool
  deriving Inhabited

/-- The switcher's rows: the current entry first, then the others in, then
the pending joins; each with its index in the entries. A row's tap selects
by that index, never by what the row shows (two entries may show the same
name and community). Laws: `switcherOrder_sound` (each row's index is the
entry it draws) and `switcherOrder_complete` (every entry has a row). -/
def switcherOrder (es : Array Entry) : List (Nat × Entry) :=
  let ix := (List.range es.size).filterMap fun i => es[i]?.map (i, ·)
  ix.filter (·.2.current) ++ ix.filter (fun p => !p.2.current && !p.2.waiting) ++
    ix.filter (fun p => !p.2.current && p.2.waiting)

theorem ix_sound (es : Array Entry) {p : Nat × Entry}
    (h : p ∈ (List.range es.size).filterMap fun i => es[i]?.map (i, ·)) : es[p.1]? = some p.2 := by
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at h
  obtain ⟨i, _, e, he, rfl⟩ := h
  exact he

/-- **A row's index is the entry it draws.** -/
theorem switcherOrder_sound (es : Array Entry) {p : Nat × Entry} (h : p ∈ switcherOrder es) :
    es[p.1]? = some p.2 := by
  unfold switcherOrder at h
  simp only [List.mem_append, List.mem_filter] at h
  rcases h with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact ix_sound es h

/-- **Every entry has a row.** -/
theorem switcherOrder_complete (es : Array Entry) (i : Nat) (hi : i < es.size) :
    ∃ p ∈ switcherOrder es, p.1 = i := by
  have hm : (i, es[i]) ∈ (List.range es.size).filterMap fun i => es[i]?.map (i, ·) := by
    simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
    exact ⟨i, hi, es[i], by simp, rfl⟩
  refine ⟨(i, es[i]), ?_, rfl⟩
  unfold switcherOrder
  simp only [List.mem_append, List.mem_filter]
  by_cases hc : es[i].current
  · exact Or.inl (Or.inl ⟨hm, by simp [hc]⟩)
  · by_cases hw : es[i].waiting
    · exact Or.inr ⟨hm, by simp [hc, hw]⟩
    · exact Or.inl (Or.inr ⟨hm, by simp [hc, hw]⟩)

/-- The community switcher, libquiet's left panel: the current community
first, outlined, with Add members; the others; pending joins as muted
rows (their id, "Waiting for a member to let you in.", a "joining"
chip); then Join a community and Create a community. -/
def switcher (f : Font) (dm : Dim) (W h : Nat) (es : Array Entry) (asking : Nat) (canInvite : Bool) : Page := Id.run do
  let pw := min W (dm.px 320)
  let mut b := blank W h dm.theme
  -- the conversation behind the panel is dimmed
  b := b.fill pw 0 W h (Palette.color dm.theme .scrim)
  let mut taps := #[]
  let rh := dm.px 76
  let d := dm.px 48
  let mut y := dm.px 8
  for (idx, e) in switcherOrder es do
    let ax := dm.px 24
    let ay := y + (rh - d) / 2
    if dm.hot 0 y pw rh (!e.waiting) then b := b.fill 0 y pw (y + rh) (Palette.color dm.theme .selected)
    if e.current then
      b := b.round (ax - 3) (ay - 3) (ax + d + 3) (ay + d + 3) (dm.px 6) (Palette.color dm.theme .accentInk)
    b := b.round ax ay (ax + d) (ay + d) (dm.px 4) (avatarColor e.id8)
    let initial := if e.waiting then String.ofList (e.id8.toList.take 2) else String.ofList [(e.name.toList.headD '?').toUpper]
    let iw := Paint.Line.width f (oneLine f f.cell initial)
    b := b.line f (oneLine f f.cell initial) (ax + (d - iw) / 2) (ay + (d - f.cell) / 2) (Palette.color dm.theme .onAccent)
    let tx := ax + d + dm.px 16
    let right := if e.current && canInvite then dm.px 56 else if e.waiting then dm.px 88 else dm.px 16
    if e.waiting then
      b := b.line f (oneLine f (pw - tx - right) s!"<{e.id8}>") tx (y + dm.px 14) (Palette.color dm.theme .muted)
      b := b.line f (oneLine f (pw - tx - right) "Waiting for a member to let you in.") tx (y + dm.px 14 + f.cell) (Palette.color dm.theme .muted)
      let cl := oneLine f (dm.px 80) "joining"
      let cw := Paint.Line.width f cl + dm.px 16
      let cx := pw - dm.px 12 - cw
      let cy := y + (rh - dm.px 28) / 2
      b := b.round cx cy (cx + cw) (cy + dm.px 28) (dm.px 14) (Palette.color dm.theme .edge)
      b := b.round (cx + 2) (cy + 2) (cx + cw - 2) (cy + dm.px 28 - 2) (dm.px 14 - 2) (Palette.color dm.theme .bg)
      b := b.line f cl (cx + dm.px 8) (cy + (dm.px 28 - f.cell) / 2) (Palette.color dm.theme .muted)
    else
      b := b.line f (oneLine f (pw - tx - right) ((if e.current then Cue.caption dm.theme .selected ++ " " else "") ++
        (if e.unread > 0 then s!"{Cue.caption dm.theme .unread} {e.unread} · " else "") ++ e.name)) tx (y + (rh - f.cell) / 2) (Palette.color dm.theme .fg)
    if e.current && canInvite then
      let gx := pw - dm.px 48
      b := b.line f (oneLine f f.cell "☺+") gx (y + (rh - f.cell) / 2) (Palette.color dm.theme .fg)
      taps := taps.push (⟨gx - dm.px 8, y, dm.px 56, rh⟩, .addMembers)
    if e.unread > 0 then
      b := Overlay.badge dm.theme b (ax + d - dm.px 10) (ay - dm.px 8) (dm.px 24) (dm.px 20) (dm.px 10) (max 2 (dm.px 2))
    taps := taps.push (⟨0, y, pw - (if e.current && canInvite then dm.px 56 else 0), rh⟩, .switchTo idx)
    y := y + rh
  y := y + dm.px 16
  -- the rows after: icon squares, as libquiet draws them
  let extra : Array (String × String × Act) :=
    (if canInvite && asking > 0 then #[("⏳", s!"Waiting to join · {asking}", Act.requests)] else #[]) ++
    #[("☺+", "Join a community", Act.joinCommunity), ("+", "Create a community", Act.createCommunity)]
  for (icon, label, act) in extra do
    if dm.hot 0 y pw (dm.px 64) then b := b.fill 0 y pw (y + dm.px 64) (Palette.color dm.theme .selected)
    let ax := dm.px 24
    let ay := y + (dm.px 64 - d) / 2
    b := b.round ax ay (ax + d) (ay + d) (dm.px 6) (Palette.color dm.theme .panel)
    let iw := Paint.Line.width f (oneLine f (2 * f.cell) icon)
    b := b.line f (oneLine f (2 * f.cell) icon) (ax + (d - iw) / 2) (ay + (d - f.cell) / 2) (Palette.color dm.theme .fg)
    b := b.line f (oneLine f (pw - ax - d - dm.px 32) label) (ax + d + dm.px 16) (y + (dm.px 64 - f.cell) / 2) (Palette.color dm.theme .fg)
    taps := taps.push (⟨0, y, pw, dm.px 64⟩, act)
    y := y + dm.px 64
  -- a tap on the dimmed conversation closes the panel
  taps := taps.push (⟨pw, 0, W - pw, h⟩, .back)
  return ⟨b, taps⟩

/-- Read a compact label in full, page by page, or copy it verbatim. -/
def label (f : Font) (dm : Dim) (W h : Nat) (text : String) (page : Nat) : Page :=
  let b := Label.paint f dm W h text page
  let (b, copy, _) := button f dm b "Copy full text" (h - dm.px 144) false .copyLabel
  let (b, next, _) := button f dm b "Next" (h - dm.px 96) false .labelNext
  let (b, prev, _) := button f dm b "Previous" (h - dm.px 48) false .labelPrev
  ⟨b, #[copy, next, prev]⟩

end Pages
