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
  let k := dm.px 48
  let dy := y + dm.px 4
  let mut deck := #[]
  let acts := #[Hit.addPhotos, .takePhoto, .emoji, .mention, .voice]
  for i in [0:acts.size] do
    deck := deck.push (⟨dm.px 4 + i * (k + dm.px 4), dy, k, k⟩, acts[i]!)
  let send : Box := ⟨W - dm.px 8 - k, dy, k, k⟩
  return ⟨dy + k + dm.px 8, tx, ty, tw, lines, cs, chipsY, deck, send⟩

/-- A glyph at 3/2 of the font's cell (nearest; Unifont is already
smoothed), its top left at (x, y). -/
def bigGlyph (f : Font) (b : Bitmap) (ch : UInt32) (x y : Nat) (c : Color) : Bitmap := Id.run do
  let g := f.glyph ch
  let n := f.adv g
  let mut b := b
  for ty in [0:f.cell * 3 / 2] do
    let bits := f.row g (ty * 2 / 3)
    if bits == 0 then continue
    b := b.modify (y + ty) fun row => Id.run do
      let mut row := row
      for tx in [0:n * 3 / 2] do
        if bits &&& (0x8000000000000000 >>> (tx * 2 / 3).toUInt64) != 0 then row := setPx row (x + tx) c
      return row
  return b

/-- An outline: a rounded box of colour c, its inside back to the ground. -/
def ring (b : Bitmap) (x0 y0 x1 y1 r k : Nat) (c ground : Color) : Bitmap :=
  (b.round x0 y0 x1 y1 r c).round (x0 + k) (y0 + k) (x1 - k) (y1 - k) (r - min r k) ground

/-- The deck's icons, drawn as outlines S pixels square (libquiet's are
line icons): a photo with a plus, a camera, a face, an at sign, a
microphone. -/
def icon (f : Font) (dm : Dim) (b : Bitmap) (h : Hit) (x y S : Nat) (c ground : Color) : Bitmap := Id.run do
  let k := max 2 (dm.px 2)
  match h with
  | .addPhotos =>
    let mut b := ring b x (y + S / 8) (x + S * 7 / 8) (y + S) (S / 8) k c ground
    -- a hill and the sun
    b := b.round (x + S / 6) (y + S * 5 / 8) (x + S * 5 / 8) (y + S * 7 / 8) (S / 6) c
    b := b.round (x + S / 2) (y + S * 3 / 8) (x + S * 5 / 8) (y + S / 2) (S / 16) c
    -- the plus, at the corner
    b := b.fill (x + S * 3 / 4) (y - S / 8 + S / 6) (x + S + k / 2) (y - S / 8 + S / 6 + k) c
    b := b.fill (x + S * 7 / 8 - k / 2 + 1) (y - S / 8) (x + S * 7 / 8 + k / 2 + 1) (y + S / 4 + S / 6) c
    return b
  | .takePhoto =>
    let mut b := ring b x (y + S / 4) (x + S) (y + S) (S / 8) k c ground
    b := b.round (x + S / 3) (y + S / 8) (x + S * 2 / 3) (y + S / 4 + k) (S / 16) c
    b := ring b (x + S * 5 / 16) (y + S * 7 / 16) (x + S * 11 / 16) (y + S * 13 / 16) (S * 3 / 16) k c ground
    return b
  | .emoji =>
    let mut b := ring b x y (x + S) (y + S) (S / 2) k c ground
    let e := max 3 (S / 10)
    b := b.round (x + S * 5 / 16) (y + S * 3 / 8) (x + S * 5 / 16 + e) (y + S * 3 / 8 + e) (e / 2) c
    b := b.round (x + S * 11 / 16 - e) (y + S * 3 / 8) (x + S * 11 / 16) (y + S * 3 / 8 + e) (e / 2) c
    -- the smile: the lower half of a ring
    let sb := ring (Bitmap.blank S S (solid ground S)) (S / 4) (S / 4) (S * 3 / 4) (S * 3 / 4 + k) (S / 4) k c ground
    for r in [S * 5 / 8:S * 3 / 4 + k] do
      if let some row := sb.rows[r]? then
        b := b.modify (y + r) fun dst => (row.extract (4 * (S / 4)) (4 * (S * 3 / 4))).copySlice 0 dst (4 * (x + S / 4)) (4 * (S / 2))
    return b
  | .mention => return bigGlyph f b 0x40 (x + (S - f.cell * 3 / 4) / 2) (y + (S - f.cell * 3 / 2) / 2) c
  | .voice =>
    let mut b := ring b (x + S * 5 / 16) y (x + S * 11 / 16) (y + S * 5 / 8) (S * 3 / 16) k c ground
    -- the stand: a cup and a stem
    let cup := ring (Bitmap.blank S S (solid ground S)) (S / 5) (S / 6) (S * 4 / 5) (S * 3 / 4) (S * 3 / 10) k c ground
    for r in [S * 7 / 16:S * 3 / 4] do
      if let some row := cup.rows[r]? then
        b := b.modify (y + r) fun dst => Id.run do
          let mut dst := dst
          for i in [S / 5:S * 4 / 5] do
            let v := getPx row i
            if v != ground then dst := setPx dst (x + i) v
          return dst
    b := b.fill (x + S / 2 - k / 2) (y + S * 3 / 4) (x + S / 2 + k / 2 + 1) (y + S * 15 / 16) c
    b := b.fill (x + S * 5 / 16) (y + S * 15 / 16 - k) (x + S * 11 / 16) (y + S * 15 / 16) c
    return b
  | _ => return b

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
  -- the icons at 3/2 of the text's size (26 dp), centred in their keys
  let S := dm.px 26
  let ground := getPx bgRow 0
  for (bx, h) in l.deck do
    b := icon f dm b h (bx.x + (bx.w - S) / 2) (bx.y + (bx.h - S) / 2) S dim ground
  let full := !text.trimAscii.isEmpty || !chips.isEmpty
  let sw := f.adv (f.glyph 0x27A4) * 3 / 2
  b := bigGlyph f b 0x27A4 (l.send.x + (l.send.w - sw) / 2) (l.send.y + (l.send.h - f.cell * 3 / 2) / 2)
    (if full then sendBlue else sendGrey)
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
