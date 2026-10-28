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
import Quiet.Row

namespace Pages
open Paint Text Font Row

/-! ## Theme (libquiet's dark Stage) -/

def card : Color := 0x26292E
def cardLine : Color := 0x3A3D41
def primary : Color := 0x5B2A86
def primaryInk : Color := 0xFFFFFF
def link : Color := 0x4C9BF5
def logo : Color := 0xE0BFF2
def warnInk : Color := 0xF5C542
def errorInk : Color := 0xF06C6C

/-- What a tap on a page does. -/
inductive Act where
  | back
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
  | none
  deriving BEq, Inhabited, Repr

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
  let mut b := b.round x0 y x1 (y + h) (dm.px 16) cardLine
  let e := max 2 (dm.px 1)
  b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 16 - e) card
  let mut taps := #[]
  for i in [0:items.size] do
    let (icon, label, act) := items[i]!
    let ry := y + i * rh
    if i > 0 then b := b.fill (x0 + e) ry (x1 - e) (ry + max 1 (dm.px 1) / 2 + 1) cardLine
    let ty := ry + (rh - f.cell) / 2
    b := b.line f (oneLine f (f.cell * 2) icon) (x0 + dm.px 16) ty ink
    b := b.line f (oneLine f (x1 - x0 - dm.px 120) label) (x0 + dm.px 16 + f.cell + dm.px 16) ty nameInk
    b := b.line f (oneLine f f.cell "›") (x1 - dm.px 16 - f.cell / 2) ty dim
    taps := taps.push (⟨x0, ry, x1 - x0, rh⟩, act)
  return (b, taps, h)

/-- A wide button: primary (filled) or secondary (outlined). -/
def button (f : Font) (dm : Dim) (b : Bitmap) (label : String) (y : Nat) (filled : Bool) (act : Act) :
    Bitmap × (Box × Act) × Nat := Id.run do
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 48
  let mut b := b
  if filled then
    b := b.round x0 y x1 (y + h) (dm.px 12) primary
  else
    let e := max 2 (dm.px 1)
    b := b.round x0 y x1 (y + h) (dm.px 12) cardLine
    b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 12 - e) Row.bg
  b := centred f b label (y + (h - f.cell) / 2) primaryInk
  return (b, (⟨x0, y, x1 - x0, h⟩, act), h)

/-- A one-line field (the keyboard's text): its box, the text or a
placeholder, the caret, and an error edge. -/
def field (f : Font) (dm : Dim) (b : Bitmap) (y : Nat) (text placeholder : String) (focused : Bool)
    (bad : Bool) : Bitmap × (Box × Act) × Nat := Id.run do
  let x0 := dm.px 16
  let x1 := b.w - dm.px 16
  let h := dm.px 52
  let e := max 2 (dm.px 1)
  let mut b := b.round x0 y x1 (y + h) (dm.px 10) (if bad then errorInk else if focused then accent else cardLine)
  b := b.round (x0 + e) (y + e) (x1 - e) (y + h - e) (dm.px 10 - e) selBg
  let ty := y + (h - f.cell) / 2
  let w := x1 - x0 - dm.px 32
  -- a long link shows its end, where the caret is
  let l := if text.isEmpty then oneLine f w placeholder else
    let full := oneLine f (10 * b.w) text
    let fw := Paint.Line.width f full
    if fw ≤ w then full else (full.filter (·.x + fw ≥ w + f.cell)).map fun g => { g with x := g.x + w - fw }
  b := b.line f l (x0 + dm.px 16) ty (if text.isEmpty then dim else nameInk)
  if focused then
    let cx := x0 + dm.px 16 + (if text.isEmpty then 0 else min w (Paint.Line.width f l))
    b := b.fill cx ty (cx + e + 1) (ty + f.cell) accent
  return (b, (⟨x0, y, x1 - x0, h⟩, .field), h)

/-- A page's bar: a back arrow or a cross on the left, the title centred. -/
def bar (f : Font) (dm : Dim) (W insetTop : Nat) (title : String) (cross : Bool) : Bitmap := Id.run do
  let h := insetTop + dm.px 56
  let mut b := Bitmap.blank W h (solid Row.bg W)
  let ty := insetTop + (dm.px 56 - f.cell) / 2
  b := b.line f (oneLine f f.cell (if cross then "✕" else "←")) (dm.px 16) ty nameInk
  b := centred f b title ty nameInk true
  return b

/-- The bar's back target, in the bar's own rows. -/
def barBack (dm : Dim) (insetTop : Nat) : Box := ⟨0, insetTop, dm.px 64, dm.px 56⟩

/-- The heading a Stage opens with, 24 dp under the bar. -/
def heading (f : Font) (dm : Dim) (b : Bitmap) (s : String) (y : Nat) : Bitmap × Nat :=
  (centred f b s y nameInk true, f.cell + dm.px 8)

def blank (W h : Nat) : Bitmap := Bitmap.blank W h (solid Row.bg W)

/-! ## The pages -/

/-- Get started: the wordmark, then join or create. (Device linking is
left out for now.) -/
def getStarted (f : Font) (dm : Dim) (W h : Nat) : Page := Id.run do
  let mut b := blank W h
  let ly := dm.px 72
  let d := dm.px 64
  let lx := (W - d - dm.px 16 - 5 * f.cell / 2) / 2
  b := b.round lx ly (lx + d) (ly + d) (d / 2) logo
  b := b.line f (oneLine f f.cell "Q") (lx + (d - f.cell / 2) / 2) (ly + (d - f.cell) / 2) Row.bg true
  b := b.line f (oneLine f (W / 2) "Quiet") (lx + d + dm.px 16) (ly + (d - f.cell) / 2) logo true
  let (b1, hh) := heading f dm b "Let’s get started…" (ly + d + dm.px 32)
  b := b1
  let y := ly + d + dm.px 32 + hh + dm.px 16
  let (b2, taps, rh) := rows f dm b y #[("+", "Join a community", .joinCommunity), ("✚", "Create a new community", .createCommunity)]
  b := b2
  let (b3, _) := para f dm b "⚠ Quiet is in beta and shouldn't be used for activities requiring security." (dm.px 24) (y + rh + dm.px 12) (W - dm.px 48) dim
  return ⟨b3, taps⟩

/-- Create a community: a heading, the name field, Continue. -/
def create (f : Font) (dm : Dim) (W h : Nat) (name : String) (focused : Bool) : Page := Id.run do
  let mut b := blank W h
  let (b1, hh) := heading f dm b "Create a community" (dm.px 24)
  let fy := dm.px 24 + hh + dm.px 40
  let (b2, ft, fh) := field f dm b1 fy name "Community name" focused false
  let (b3, bt, _) := button f dm b2 "Continue" (fy + fh + dm.px 24) (!name.trimAscii.isEmpty) .continue_
  b := b3
  return ⟨b, #[ft, bt]⟩

/-- Join community: invite link or QR code. -/
def joinChoice (f : Font) (dm : Dim) (W h : Nat) (status : Option String) : Page := Id.run do
  let mut b := blank W h
  let (b1, hh) := heading f dm b "Join community" (dm.px 24)
  let mut y := dm.px 24 + hh + dm.px 24
  b := b1
  if let some st := status then
    let (b2, ph) := para f dm b st (dm.px 24) y (W - dm.px 48) errorInk
    b := b2; y := y + ph + dm.px 12
  let (b3, taps, _) := rows f dm b y #[("⛓", "Join with invite link", .inviteLink), ("▦", "Join with QR code", .qrCode)]
  return ⟨b3, taps⟩

/-- Join with invite link: the explainer, and the sentence-button that
opens the paste field. -/
def openInvite (f : Font) (dm : Dim) (W h : Nat) : Page := Id.run do
  let mut b := blank W h
  let (b1, hh) := heading f dm b "Join with invite link" (dm.px 24)
  let (b2, ph) := para f dm b1 "Open an invite link from a community admin. (If you just installed Quiet, open the invite again!)"
    (dm.px 24) (dm.px 24 + hh + dm.px 16) (W - dm.px 48) ink
  let y := dm.px 24 + hh + dm.px 16 + ph + dm.px 24
  let l := oneLine f W "Paste a link"
  let w := Paint.Line.width f l
  b := b2.line f l ((W - w) / 2) y link
  return ⟨b, #[(⟨(W - w) / 2, y, w, f.cell⟩, .pasteLink)]⟩

/-- Paste a link to join: one field, one button; a refusal under it. -/
def paste (f : Font) (dm : Dim) (W h : Nat) (text : String) (focused : Bool) (refusal : Option String) : Page := Id.run do
  let mut b := blank W h
  let (b1, hh) := heading f dm b "Paste a link to join" (dm.px 24)
  let fy := dm.px 24 + hh + dm.px 40
  let (b2, ft, fh) := field f dm b1 fy text "quiet://join/…" focused refusal.isSome
  b := b2
  let mut y := fy + fh + dm.px 8
  if let some r := refusal then
    let (b3, ph) := para f dm b r (dm.px 16) y (W - dm.px 32) errorInk
    b := b3; y := y + ph
  let (b4, bt, _) := button f dm b "Continue" (y + dm.px 16) (!text.trimAscii.isEmpty) .continue_
  return ⟨b4, #[ft, bt]⟩

/-- Join with QR code: the camera's square (its frames, or why there are
none), the instruction, and the way to paste instead. -/
def scan (f : Font) (dm : Dim) (W h : Nat) (camera : Option Bitmap) (note : String) : Page := Id.run do
  let mut b := blank W h
  let s := min (W - dm.px 96) (h / 2)
  let x := (W - s) / 2
  let y := dm.px 24
  match camera with
  | some img => b := b.image img x y (dm.px 12)
  | none =>
    b := b.round x y (x + s) (y + s) (dm.px 12) 0x000000
    b := centred f b note (y + (s - f.cell) / 2) nameInk
  let (b2, ph) := para f dm b "Point the camera at the QR code on the other device." (dm.px 24) (y + s + dm.px 24) (W - dm.px 48) ink
  let ly := y + s + dm.px 24 + ph + dm.px 24
  let l := oneLine f W "Paste a link to join"
  let w := Paint.Line.width f l
  b := b2.line f l ((W - w) / 2) ly link
  return ⟨b, #[(⟨(W - w) / 2, ly, w, f.cell⟩, .pasteLink)]⟩

/-- Agree & join: what joining means, and the one button. -/
def agree (f : Font) (dm : Dim) (W h : Nat) (community : String) : Page := Id.run do
  let mut b := blank W h
  let text := s!"Joining {community} shares your device's public key and what you post with its members, and gives them your history from here on. This community may include an always-on cloud server, which cannot read what is said here but sees who is in the community and when they post."
  let (b1, ph) := para f dm b text (dm.px 16) (dm.px 24) (W - dm.px 32) ink
  let (b2, bt, _) := button f dm b1 "Agree & Join" (dm.px 24 + ph + dm.px 24) true .agree
  b := b2
  return ⟨b, #[bt]⟩

/-- Waiting to join: asked, and not yet approved. -/
def waiting (f : Font) (dm : Dim) (W h : Nat) (community : String) : Page := Id.run do
  let mut b := blank W h
  let d := dm.px 72
  let y := dm.px 48
  b := b.round ((W - d) / 2) y ((W + d) / 2) (y + d) (d / 2) cardLine
  b := b.line f (oneLine f f.cell "⏳") ((W - f.cell) / 2) (y + (d - f.cell) / 2) ink
  let (b1, hh) := heading f dm b "Waiting to join" (y + d + dm.px 24)
  let (b2, _) := para f dm b1 s!"You asked to join {community}. Once a member approves, you can read and post here." (dm.px 24) (y + d + dm.px 24 + hh + dm.px 8) (W - dm.px 48) dim
  return ⟨b2, #[]⟩

/-- One device asking to join. -/
structure Asking where
  device : String
  when : String
  going : Bool
  deriving Inhabited

/-- Join requests: who is waiting, each with approve and hide; or none,
and the way to add members. -/
def requests (f : Font) (dm : Dim) (W h : Nat) (asking : Array Asking) : Page := Id.run do
  let mut b := blank W h
  let mut taps := #[]
  if asking.isEmpty then
    b := centred f b "No one is waiting to join" (dm.px 72) nameInk true
    let l := oneLine f W "Add members"
    let w := Paint.Line.width f l + dm.px 32
    let x := (W - w) / 2
    let y := dm.px 72 + f.cell + dm.px 24
    b := b.round x y (x + w) (y + dm.px 44) (dm.px 22) cardLine
    b := b.round (x + 2) (y + 2) (x + w - 2) (y + dm.px 44 - 2) (dm.px 22 - 2) card
    b := b.line f l (x + dm.px 16) (y + (dm.px 44 - f.cell) / 2) nameInk
    return ⟨b, #[(⟨x, y, w, dm.px 44⟩, .addMembers)]⟩
  b := b.line f (oneLine f W s!"{asking.size} waiting") (dm.px 16) (dm.px 16) dim
  let rh := dm.px 64
  for i in [0:asking.size] do
    let a := asking[i]!
    let y := dm.px 16 + f.cell + dm.px 8 + i * rh
    let d := dm.px 32
    b := b.round (dm.px 16) (y + (rh - d) / 2) (dm.px 16 + d) (y + (rh + d) / 2) (dm.px 6) cardLine
    b := b.line f (oneLine f f.cell "?") (dm.px 16 + (d - f.cell / 2) / 2) (y + (rh - f.cell) / 2) ink
    let tx := dm.px 16 + d + dm.px 12
    b := b.line f (oneLine f (W / 2) a.device) tx (y + dm.px 4) nameInk true
    b := b.line f (oneLine f (W / 2) s!"New person · {a.when}") tx (y + dm.px 4 + f.cell) dim
    -- approve (a check) and hide (a cross), right-aligned
    let k := dm.px 40
    let ax := W - dm.px 16 - k
    let hx := ax - dm.px 8 - k
    let ky := y + (rh - k) / 2
    b := b.round hx ky (hx + k) (ky + k) (k / 2) cardLine
    b := b.line f (oneLine f f.cell "✕") (hx + (k - f.cell / 2) / 2) (ky + (k - f.cell) / 2) ink
    b := b.round ax ky (ax + k) (ky + k) (k / 2) (if a.going then cardLine else primary)
    b := b.line f (oneLine f f.cell (if a.going then "…" else "✓")) (ax + (k - f.cell / 2) / 2) (ky + (k - f.cell) / 2) primaryInk
    taps := taps.push (⟨hx, ky, k, k⟩, .hide i) |>.push (⟨ax, ky, k, k⟩, .approve i)
  return ⟨b, taps⟩

/-- Add members: the QR code (or its square while there is none), the
share button, the link with Copy, the caution, what happens next. -/
def invite (f : Font) (dm : Dim) (W h : Nat) (qr : Option Bitmap) (linkText : String) : Page := Id.run do
  let mut b := blank W h
  let s := min (W - dm.px 128) (h / 3)
  let x := (W - s) / 2
  let y := dm.px 24
  b := b.round (x - dm.px 16) (y - dm.px 16) (x + s + dm.px 16) (y + s + dm.px 16) (dm.px 12) cardLine
  b := b.round (x - dm.px 15) (y - dm.px 15) (x + s + dm.px 15) (y + s + dm.px 15) (dm.px 12) Row.bg
  match qr with
  | some q => b := b.image q x y (dm.px 8)
  | none => b := b.round x y (x + s) (y + s) (dm.px 8) 0xFFFFFF
  let mut yy := y + s + dm.px 32
  b := centred f b "Scan with the Quiet app to ask to join." yy dim
  yy := yy + f.cell + dm.px 24
  let (b1, st, sh) := button f dm b "Share invite link" yy true .share
  b := b1
  yy := yy + sh + dm.px 16
  -- the link and Copy
  let lx0 := dm.px 16
  let lx1 := W - dm.px 16
  let cw := dm.px 72
  let ls := Text.layout f (lx1 - lx0 - cw - dm.px 32) linkText
  let lh := max (dm.px 56) (ls.size * dm.lineH + dm.px 16)
  b := b.round lx0 yy lx1 (yy + lh) (dm.px 10) cardLine
  b := b.round (lx0 + 2) (yy + 2) (lx1 - 2) (yy + lh - 2) (dm.px 10 - 2) Row.bg
  for i in [0:ls.size] do
    b := b.line f ls[i]! (lx0 + dm.px 16) (yy + dm.px 8 + i * dm.lineH) dim
  let cx := lx1 - dm.px 8 - cw
  let cy := yy + (lh - dm.px 40) / 2
  b := b.round cx cy (cx + cw) (cy + dm.px 40) (dm.px 20) cardLine
  b := b.round (cx + 2) (cy + 2) (cx + cw - 2) (cy + dm.px 40 - 2) (dm.px 20 - 2) Row.bg
  b := centred f (Bitmap.blank cw f.cell (solid Row.bg cw)) "Copy" 0 nameInk |>.rows.foldl (fun (acc : Bitmap × Nat) row =>
    (acc.1.modify (cy + (dm.px 40 - f.cell) / 2 + acc.2) (fun r => row.copySlice 0 r (4 * cx) (4 * cw)), acc.2 + 1)) (b, 0) |>.1
  let ct : Box × Act := (⟨cx, cy, cw, dm.px 40⟩, .copy)
  yy := yy + lh + dm.px 16
  let (b2, ph) := para f dm b "Anyone holding this link or code can ask to join, and a link can't be cancelled once it's sent. Share it only with people you trust." (dm.px 16) yy (W - dm.px 32) dim
  b := b2
  yy := yy + ph + dm.px 24
  b := b.line f (oneLine f W "What happens next") (dm.px 16) yy dim true
  yy := yy + dm.lineH + dm.px 8
  let steps := #["1. They open the link, or scan the code, in Quiet.", "2. Their device appears under Waiting to join.",
    "3. Once a member vouches for them, they can read and post here."]
  for st in steps do
    let (b3, sh2) := para f dm b st (dm.px 16) yy (W - dm.px 32) nameInk
    b := b3
    yy := yy + sh2 + dm.px 8
  return ⟨b, #[st, ct]⟩

/-- One community in the switcher. -/
structure Entry where
  name : String
  unread : Nat
  current : Bool
  waiting : Bool
  deriving Inhabited

/-- The community switcher: every community, the current one marked, a
waiting one marked as such, and Add a community. -/
def switcher (f : Font) (dm : Dim) (W h : Nat) (es : Array Entry) : Page := Id.run do
  let mut b := blank W h
  let mut taps := #[]
  let rh := dm.px 64
  let d := dm.px 40
  for i in [0:es.size] do
    let e := es[i]!
    let y := dm.px 8 + i * rh
    if e.current then b := b.fill 0 y W (y + rh) selBg
    let ax := dm.px 16
    let ay := y + (rh - d) / 2
    b := b.round ax ay (ax + d) (ay + d) (dm.px 10) (if e.waiting then cardLine else primary)
    let initial := String.ofList [(e.name.toList.headD '?').toUpper]
    b := b.line f (oneLine f f.cell initial) (ax + (d - f.cell / 2) / 2) (ay + (d - f.cell) / 2) primaryInk true
    let tx := ax + d + dm.px 16
    b := b.line f (oneLine f (W - tx - dm.px 80) e.name) tx (y + (rh - f.cell) / 2 - (if e.waiting then dm.px 10 else 0)) nameInk true
    if e.waiting then
      b := b.line f (oneLine f (W / 2) "Waiting to join") tx (y + (rh - f.cell) / 2 + dm.px 12) dim
    if e.unread > 0 then
      let t := if e.unread > 99 then "99+" else toString e.unread
      let l := oneLine f (W / 4) t
      let w := Paint.Line.width f l + dm.px 16
      let bx := W - dm.px 16 - w
      let by0 := y + (rh - dm.px 28) / 2
      b := b.round bx by0 (bx + w) (by0 + dm.px 28) (dm.px 14) accent
      b := b.line f l (bx + dm.px 8) (by0 + (dm.px 28 - f.cell) / 2) primaryInk
    taps := taps.push (⟨0, y, W, rh⟩, .switchTo i)
  let y := dm.px 8 + es.size * rh + dm.px 8
  let (b2, t2, _) := rows f dm b y #[("+", "Add a community", .addCommunity)]
  return ⟨b2, taps ++ t2⟩

end Pages
