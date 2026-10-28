/-
The composer, libquiet's on a phone: the text field (growing to five
lines), the attached photos as 64 dp chips (each with its X and its size,
"4.0 KiB · 91% smaller"), and the deck: Add photos, Take a photo, Choose
emoji, Mention someone, Record a voice message, and Send on the right
(grey with nothing to send, blue otherwise).

`layout` places every part once; `paint` draws them there and `hit`
answers taps from the same boxes.
-/
import Quiet.Row

namespace Composer
open Paint Text Font Row

/-- An attached photo: its thumbnail (64 dp square, cropped) and its
caption. -/
structure Chip where
  thumb : Bitmap
  caption : String
  deriving Inhabited

inductive Hit where
  | text | addPhotos | takePhoto | emoji | mention | voice | send | removeChip (i : Nat) | none
  deriving BEq, Repr, Inhabited

structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Inhabited

def Box.has (b : Box) (x y : Nat) : Bool := b.x ≤ x && x < b.x + b.w && b.y ≤ y && y < b.y + b.h

/-- The most photos a message attaches (libquiet's). -/
def maxChips : Nat := 4

def sendBlue : Color := 0x1B6FEC
def sendGrey : Color := 0x7F7F7F
def line : Color := 0x3A3D41

structure Layout where
  h : Nat
  textX : Nat
  textY : Nat
  textW : Nat
  lines : Array Line
  chips : Array (Box × Box)   -- the thumbnail, its X
  chipsY : Nat
  deck : Array (Box × Hit)
  send : Box

def layout (f : Font) (dm : Dim) (W : Nat) (text : String) (chips : Nat) : Layout := Id.run do
  let pad := dm.px 16
  let tx := pad
  let tw := W - 2 * pad
  let lines := if text.isEmpty then #[#[]] else Text.layout f tw text
  let ty := dm.px 12
  let mut y := ty + (min 5 lines.size) * dm.lineH + dm.px 8
  let chipsY := y
  let c := dm.px 64
  let mut cs := #[]
  for i in [0:chips] do
    let x := pad + i * (c + dm.px 12)
    let xb := dm.px 24
    cs := cs.push (⟨x, y, c, c⟩, ⟨x + c - xb + dm.px 6, y - dm.px 6, xb, xb⟩)
  if chips > 0 then y := y + c + dm.px 4 + 3 * dm.lineH
  let k := dm.px 44
  let dy := y + dm.px 4
  let mut deck := #[]
  let acts := #[Hit.addPhotos, .takePhoto, .emoji, .mention, .voice]
  for i in [0:acts.size] do
    deck := deck.push (⟨dm.px 4 + i * (k + dm.px 4), dy, k, k⟩, acts[i]!)
  let send : Box := ⟨W - dm.px 8 - k, dy, k, k⟩
  return ⟨dy + k + dm.px 8, tx, ty, tw, lines, cs, chipsY, deck, send⟩

def glyphOf : Hit → String
  | .addPhotos => "⊞" | .takePhoto => "◉" | .emoji => "☺" | .mention => "@" | .voice => "♪"
  | _ => ""

/-- The composer's pixels; `caret` is the caret's line and x, if focused. -/
def paint (f : Font) (dm : Dim) (W : Nat) (bgRow : ByteArray) (l : Layout) (text : String)
    (placeholder : String) (chips : Array Chip) (caret : Option (Nat × Nat)) : Bitmap := Id.run do
  let mut b := Bitmap.blank W l.h bgRow
  b := b.fill 0 0 W (max 2 (dm.px 1)) line
  if text.isEmpty then
    b := b.line f (oneLine f l.textW placeholder) l.textX l.textY dim
  else
    for i in [0:min 5 l.lines.size] do
      b := b.line f l.lines[i]! l.textX (l.textY + i * dm.lineH) ink
  if let some (cl, cx) := caret then
    let cy := l.textY + (min 4 cl) * dm.lineH
    b := b.fill (l.textX + cx) cy (l.textX + cx + max 2 (dm.px 1) + 1) (cy + f.cell) accent
  for i in [0:min chips.size l.chips.size] do
    let (tb, xb) := l.chips[i]!
    b := b.image chips[i]!.thumb tb.x tb.y (dm.px 8)
    b := b.round xb.x xb.y (xb.x + xb.w) (xb.y + xb.h) (xb.w / 2) 0xF5F5F5
    b := b.line f (oneLine f f.cell "✕") (xb.x + (xb.w - f.cell / 2) / 2) (xb.y + (xb.h - f.cell) / 2) 0x333333
    let ls := Text.layout f (dm.px 76) chips[i]!.caption
    for k in [0:min 3 ls.size] do
      b := b.line f ls[k]! tb.x (tb.y + tb.h + dm.px 4 + k * dm.lineH) dim
  for (bx, h) in l.deck do
    let g := oneLine f f.cell (glyphOf h)
    b := b.line f g (bx.x + (bx.w - Paint.Line.width f g) / 2) (bx.y + (bx.h - f.cell) / 2) dim
  let full := !text.trimAscii.isEmpty || !chips.isEmpty
  let sg := oneLine f f.cell "➤"
  b := b.line f sg (l.send.x + (l.send.w - Paint.Line.width f sg) / 2) (l.send.y + (l.send.h - f.cell) / 2)
    (if full then sendBlue else sendGrey) true
  return b

def hit (l : Layout) (x y : Nat) : Hit := Id.run do
  for i in [0:l.chips.size] do
    if l.chips[i]!.2.has x y then return .removeChip i
  for (bx, h) in l.deck do
    if bx.has x y then return h
  if l.send.has x y then return .send
  if y < l.chipsY then return .text
  return .none

end Composer
