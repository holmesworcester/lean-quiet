/-
The composer, libquiet's on a phone: the text field (growing to five
lines), the attached photos as 64 dp chips (each with its X and its size,
"4.0 KiB · 91% smaller"), and the deck: Add photos, Take a photo, Choose
emoji, Mention someone, Record a voice message, and Send on the right
(grey with nothing to send, blue otherwise).

`layout` places every part once; `paint` draws them there and `hit`
answers taps from the same boxes.
-/
import engine.renderer.Row

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

def sendBlue : Color := Palette.color .dark .link
def sendGrey : Color := Palette.color .dark .muted
def line : Color := Palette.color .dark .edge

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
  lineH : Nat := 20
  wide : Bool := false
  mobile : Bool := true

/-- Chip i's thumbnail and its X, on the chips' row at y: 64 dp squares
12 dp apart from the text's left edge, the X overhanging the top right. -/
def chipBoxes (dm : Dim) (y i : Nat) : Box × Box :=
  let c := dm.px 64
  let x := dm.px 16 + i * (c + dm.px 12)
  let xb := dm.px 24
  (⟨x, y, c, c⟩, ⟨x + c - xb + dm.px 6, y - dm.px 6, xb, xb⟩)

theorem px_mono (dm : Dim) {a b : Nat} (h : a ≤ b) : dm.px a ≤ dm.px b := by
  unfold Dim.px
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _)

/-- **Chips are in order and never overlap**: chip i's thumbnail ends
before chip j's begins. -/
theorem chips_apart (dm : Dim) (y : Nat) {i j : Nat} (h : i < j) :
    (chipBoxes dm y i).1.x + (chipBoxes dm y i).1.w ≤ (chipBoxes dm y j).1.x := by
  simp only [chipBoxes]
  have : (i + 1) * (dm.px 64 + dm.px 12) ≤ j * (dm.px 64 + dm.px 12) := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at this
  omega

/-- **A chip's X never reaches the next chip**: it ends before chip j's
thumbnail (and so before its X), so a tap on it removes that chip alone. -/
theorem x_clear (dm : Dim) (y : Nat) {i j : Nat} (h : i < j) :
    (chipBoxes dm y i).2.x + (chipBoxes dm y i).2.w ≤ (chipBoxes dm y j).1.x := by
  have h24 := px_mono dm (show 24 ≤ 64 by omega)
  have h6 := px_mono dm (show 6 ≤ 12 by omega)
  simp only [chipBoxes]
  have : (i + 1) * (dm.px 64 + dm.px 12) ≤ j * (dm.px 64 + dm.px 12) := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at this
  omega

/-- **With at most `maxChips` chips, every thumbnail and X is on
screen**, on a screen as wide as the four with their gaps. -/
theorem chips_fit (dm : Dim) (y W : Nat) {i : Nat} (hi : i < maxChips)
    (hW : dm.px 16 + maxChips * (dm.px 64 + dm.px 12) ≤ W) :
    (chipBoxes dm y i).1.x + (chipBoxes dm y i).1.w ≤ W ∧
      (chipBoxes dm y i).2.x + (chipBoxes dm y i).2.w ≤ W := by
  have h24 := px_mono dm (show 24 ≤ 64 by omega)
  have h6 := px_mono dm (show 6 ≤ 12 by omega)
  simp only [chipBoxes]
  have : (i + 1) * (dm.px 64 + dm.px 12) ≤ maxChips * (dm.px 64 + dm.px 12) := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  constructor <;> omega

def layout (f : Font) (dm : Dim) (W : Nat) (text : String) (chips : Nat) (wide := false) (mobile := true) : Layout := Id.run do
  let px := dm.px
  let gutter := if wide then px 16 else 0
  let edge := px 1
  let tx := gutter + px 16 + (if wide then edge else 0)
  let tw := W - 2 * tx
  let lines := if text.isEmpty then #[#[]] else Text.layout f tw text
  let lineH := px 20
  let ty := px 13
  let mut y := px 25 + (min 5 lines.size) * lineH
  let chipsY := y
  let columns := max 1 ((W - 2 * gutter - px 16) / px 76)
  let chipH := px 68 + 3 * lineH
  let cs := (List.range chips).toArray.map fun i =>
    let (box, close) := chipBoxes dm (y + (i / columns) * chipH) (i % columns)
    ({ box with x := box.x + gutter }, { close with x := close.x + gutter })
  if chips > 0 then y := y + ((chips + columns - 1) / columns) * chipH
  let acts := if mobile then #[Hit.addPhotos, .takePhoto, .emoji, .mention, .voice]
    else #[Hit.addPhotos, .emoji, .mention, .voice]
  let k := min (px (if wide then 32 else 44)) ((W - 2 * gutter - px 16) / (acts.size + 1))
  let dy := y + px 8
  let deck := acts.mapIdx fun i act => (⟨gutter + px 8 + i * k, dy, k, k⟩, act)
  let send : Box := ⟨W - gutter - px 8 - k, dy, k, k⟩
  return ⟨dy + k + px 9 + (if wide then px 8 else 0), tx, ty, tw, lines, cs, chipsY, deck, send, lineH, wide, mobile⟩

/-- A glyph at 3/2 of the font's cell (nearest; Unifont is already
smoothed), its top left at (x, y). -/
def bigGlyph (f : Font) (b : Bitmap) (ch : UInt32) (x y : Nat) (c : Color) : Bitmap := Id.run do
  if let some ref := (f.glyph ch).noto then
    if let some ink := f.noto.bitmap ref then
      let w := ink.w * 3 / 2
      let h := ink.h * 3 / 2
      let pixels := ByteArray.mk ((Array.range (w*h)).map fun i =>
        ink.pixels[(i / w * 2 / 3) * ink.w + i % w * 2 / 3]?.getD 0)
      return b.notoGlyph { ink with x := ink.x * 3 / 2, y := ink.y * 3 / 2, w, h, pixels } x y c 0
  let g := (f.bitmapGlyph? ch).getD (f.glyph 0xFFFD)
  let n := f.adv g
  let mut b := b
  for ty in [0:f.cell * 3 / 2] do
    let bits := f.row g (ty * 2 / 3)
    if bits == 0 then continue
    b := b.modify (y + ty) fun row => Id.run do
      let mut row := row
      for tx in [0:n * 3 / 2] do
        if bits &&& (0x8000000000000000 >>> (tx * 2 / 3).toUInt64) != 0 then row := setPx row (x + tx) (textColor c row (x + tx))
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

/-- The caret's width. -/
def caretW (dm : Dim) : Nat := max 2 (dm.px 1) + 1

/-- Where the placeholder starts: past the caret at the text's start, so
the caret covers none of its glyphs (`caret_clear`). -/
def placeholderX (dm : Dim) (l : Layout) : Nat := l.textX + caretW dm + dm.px 2

/-- **The caret never covers the placeholder.** With no text the caret
is at the text's start; its right edge is at or before every placeholder
glyph's left edge. -/
theorem caret_clear (f : Font) (dm : Dim) (l : Layout) (ph : String) {g : Text.Placed}
    (_hg : g ∈ (oneLine f l.textW ph).toList) : l.textX + 0 + caretW dm ≤ placeholderX dm l + g.x := by
  unfold placeholderX; omega

/-- The composer's pixels; `caret` is the caret's line and x, if focused. -/
def paint (f : Font) (dm : Dim) (W : Nat) (bgRow : ByteArray) (l : Layout) (text : String)
    (placeholder : String) (chips : Array Chip) (caret : Option (Nat × Nat)) : Bitmap := Id.run do
  let mut b := Bitmap.blank W l.h bgRow
  let color := Palette.color dm.theme
  let gutter := if l.wide then dm.px 16 else 0
  let rowH := l.h - (if l.wide then dm.px 8 else 0)
  if l.wide then
    b := b.round gutter 0 (W - gutter) rowH (dm.px 16) (color .line)
    b := b.round (gutter + dm.px 1) (dm.px 1) (W - gutter - dm.px 1) (rowH - dm.px 1) (dm.px 15) (color .panel)
  else
    b := b.fill 0 0 W rowH (color .panel)
    b := b.fill 0 0 W (dm.px 1) (color .selected)
    b := b.fill 0 (l.textY + l.lines.size * l.lineH + dm.px 11) W (l.textY + l.lines.size * l.lineH + dm.px 12) (color .bg)
  if text.isEmpty then
    b := b.line f (oneLine f l.textW placeholder) (if caret.isSome then placeholderX dm l else l.textX) l.textY (Palette.color dm.theme .muted)
  else
    for i in [0:min 5 l.lines.size] do
      b := b.line f l.lines[i]! l.textX (l.textY + i * l.lineH) (Palette.color dm.theme .fg)
  if let some (cl, cx) := caret then
    let cy := l.textY + (min 4 cl) * l.lineH
    b := b.fill (l.textX + cx) cy (l.textX + cx + caretW dm) (cy + f.cell) (Palette.color dm.theme .accentInk)
  for i in [0:min chips.size l.chips.size] do
    let (tb, xb) := l.chips[i]!
    b := b.image chips[i]!.thumb tb.x tb.y (dm.px 8)
    b := b.round xb.x xb.y (xb.x + xb.w) (xb.y + xb.h) (xb.w / 2) (Palette.color dm.theme .panel)
    b := b.line f (oneLine f f.cell "✕") (xb.x + (xb.w - f.cell / 2) / 2) (xb.y + (xb.h - f.cell) / 2) (Palette.color dm.theme .fg)
    let ls := Text.layout f (dm.px 76) chips[i]!.caption
    for k in [0:min 3 ls.size] do
      b := b.line f ls[k]! tb.x (tb.y + tb.h + dm.px 4 + k * dm.lineH) (Palette.color dm.theme .muted)
  for (bx, action) in l.deck do
    let name := match action with
      | .addPhotos => if l.mobile then "image-plus" else "icon-clip"
      | .takePhoto => "camera" | .emoji => "emoji" | .mention => "mention" | .voice => "icon-mic" | _ => ""
    let size := dm.px 20
    b := b.icon f name (bx.x + (bx.w - size) / 2) (bx.y + (bx.h - size) / 2) size
      (if dm.theme == .dark then 0xa0a0a0 else 0x7f7f7f)
  let full := !text.trimAscii.isEmpty || !chips.isEmpty
  let size := dm.px 24
  b := b.icon f "send" (l.send.x + (l.send.w - size) / 2) (l.send.y + (l.send.h - size) / 2) size
    (if full then color .link else if dm.theme == .dark then 0xa0a0a0 else 0x7f7f7f)
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
