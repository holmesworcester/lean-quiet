/-
A message row: what it shows (`RowData`, read from live answers), where
each part goes (`layout`, pure), and its pixels (`paint`, pure: it runs
on a worker task, and the frame shows the last finished paint).

Slack-like, on a dark background: the author's avatar, their name in
bold and the time, the text, the pictures (each at its own aspect in a
reserved box, so a picture that decodes late moves nothing), and the
reactions as pills, the user's own outlined. A selected row also shows
the reaction palette. Every part has its own box, and the boxes do not
overlap: what one part paints, no other part paints over.
-/
import Quiet.Paint
import Quiet.Image
import Quiet.Text

namespace Row
open Paint Text Font

/-! ## Theme -/

def bg : Color := 0x1A1D21
def ink : Color := 0xD1D2D3
def nameInk : Color := 0xF8F8F8
def dim : Color := 0x9A9B9E
def pill : Color := 0x2C2F33
def pillMine : Color := 0x1D3A4A
def accent : Color := 0x1D9BD1
def selBg : Color := 0x222529
def placeholder : Color := 0x2C2F33

/-- Sizes for a screen: its density (dpi) and the font's cell. Lengths
are given in dp (Android's density-independent pixels, 160 a inch) and
drawn in pixels; text is the font's cell, about 24 dp. -/
structure Dim where
  dpi : Nat
  cell : Nat
  deriving Inhabited, BEq

def Dim.px (d : Dim) (dp : Nat) : Nat := (dp * d.dpi + 80) / 160
def Dim.pad (d : Dim) : Nat := d.px 12
def Dim.avatar (d : Dim) : Nat := d.px 40
def Dim.textX (d : Dim) : Nat := d.pad + d.avatar + d.px 12
def Dim.lineH (d : Dim) : Nat := d.cell + d.cell / 8
def Dim.topPad (d : Dim) : Nat := d.px 8
def Dim.gap (d : Dim) : Nat := d.px 6
def Dim.pillH (d : Dim) : Nat := d.cell + d.px 8

/-! ## Data -/

/-- A reaction tally: the emoji, how many people, whether one is me. -/
structure Tally where
  emoji : String
  n : Nat
  mine : Bool
  deriving BEq, Inhabited

/-- A picture: its blob's hash and size (none until the blob is known). -/
structure Pic where
  hash : ByteArray
  w : Nat
  h : Nat
  deriving BEq, Inhabited

structure RowData where
  name : String
  avatar : Option ByteArray
  text : String
  time : Nat
  pics : List Pic
  tallies : List Tally
  pending : Bool
  selected : Bool
  deriving BEq, Inhabited

/-! ## Layout -/

structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Inhabited, BEq

structure Layout where
  h : Nat
  name : Line
  time : Line
  timeX : Nat
  text : Array Line
  textY : Nat
  pics : Array Box
  /-- Pills: box, emoji, the count's line, mine. -/
  pills : Array (Box × String × Line × Bool)
  /-- The palette (selected rows): box and emoji. -/
  palette : Array (Box × String)
  deriving Inhabited

def emojiPalette : Array String := #["👍", "❤", "😂", "🎉", "🙏", "👀", "🔥", "✅"]

def clock (t : Nat) : String :=
  let m := t % 1440
  let hh := m / 60
  let mm := m % 60
  s!"{hh}:{if mm < 10 then "0" else ""}{mm}"

/-- The picture's box: at most 280 x 240 dp and the text's width, its
aspect kept. -/
def picBox (dm : Dim) (maxW : Nat) (p : Pic) : Nat × Nat :=
  let mw := min (dm.px 280) maxW
  let mh := dm.px 240
  let w := max p.w 1
  let h := max p.h 1
  if w * mh ≤ h * mw then (max 1 (w * mh / h), mh) else (mw, max 1 (h * mw / w))

def layout (f : Font) (dm : Dim) (W : Nat) (d : RowData) : Layout := Id.run do
  let tx := dm.textX
  let tw := W - tx - dm.pad
  let lh := dm.lineH
  let name := oneLine f (tw / 2) d.name
  let timeX := tx + Paint.Line.width f name + dm.px 8
  let time := oneLine f (dm.cell * 4) (if d.pending then "pending" else clock d.time)
  let text := if d.text.isEmpty then #[] else Text.layout f tw d.text
  let mut y := dm.topPad + lh
  let textY := y
  y := y + text.size * lh
  let mut pics := #[]
  for p in d.pics do
    y := y + dm.gap
    let (w, h) := picBox dm tw p
    pics := pics.push ⟨tx, y, w, h⟩
    y := y + h
  let mut pills := #[]
  let mut x := tx
  let ph := dm.pillH
  if !d.tallies.isEmpty then y := y + dm.gap
  for t in d.tallies do
    let count := oneLine f (dm.cell * 3) (toString t.n)
    let w := dm.px 10 + dm.cell + dm.px 4 + Paint.Line.width f count + dm.px 10
    if x + w > W - dm.pad then x := tx; y := y + ph + dm.gap
    pills := pills.push (⟨x, y, w, ph⟩, t.emoji, count, t.mine)
    x := x + w + dm.gap
  if !d.tallies.isEmpty then y := y + ph
  let mut palette := #[]
  if d.selected then
    y := y + dm.px 8
    let mut px := tx
    let bw := dm.cell + dm.px 12
    for e in emojiPalette do
      if px + bw > W - dm.pad then break
      palette := palette.push (⟨px, y, bw, ph⟩, e)
      px := px + bw + dm.gap
    y := y + ph
  let h := max (y + dm.px 8) (dm.topPad + dm.avatar + dm.px 8)
  return ⟨h, name, time, timeX, text, textY, pics, pills, palette⟩

/-! ## Paint -/

/-- An emoji's glyph centred in a box (its first code point). -/
def emojiAt (f : Font) (b : Bitmap) (e : String) (x y : Nat) (c : Color) : Bitmap :=
  b.glyph f (e.toList.headD ' ').val x y c false

/-- The row's pixels: the layout's parts, each in its box. av is the
avatar and imgs the pictures, each at its box's size, or none while it
decodes (a placeholder box is drawn instead). -/
def paint (f : Font) (dm : Dim) (W : Nat) (bgRow : ByteArray) (d : RowData) (l : Layout)
    (av : Option Bitmap) (imgs : Array (Option Bitmap)) : Bitmap := Id.run do
  let mut b := Bitmap.blank W l.h bgRow
  if d.selected then b := b.fill 0 0 W l.h selBg
  let tx := dm.textX
  let lh := dm.lineH
  -- glyphs sit in their line: the cell, then an eighth of it below
  let ay := dm.topPad
  let a := dm.avatar
  match av with
  | some img => b := b.image img dm.pad ay (a / 2)
  | none => b := b.round dm.pad ay (dm.pad + a) (ay + a) (a / 2) placeholder
  b := b.line f l.name tx dm.topPad nameInk true
  b := b.line f l.time l.timeX dm.topPad dim
  let tc := if d.pending then dim else ink
  for i in [0:l.text.size] do
    b := b.line f l.text[i]! tx (l.textY + i * lh) tc
  let r := dm.px 8
  for i in [0:l.pics.size] do
    let bx := l.pics[i]!
    match imgs[i]? >>= id with
    | some img => b := b.image img bx.x bx.y r
    | none => b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) r placeholder
  let pr := dm.pillH / 2
  let inset := dm.px 4
  for (bx, e, count, mine) in l.pills do
    if mine then
      b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) pr accent
      let k := max 2 (dm.px 1)
      b := b.round (bx.x + k) (bx.y + k) (bx.x + bx.w - k) (bx.y + bx.h - k) (pr - k) pillMine
    else
      b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) pr pill
    b := emojiAt f b e (bx.x + dm.px 10) (bx.y + inset) 0xF5C542
    b := b.line f count (bx.x + dm.px 10 + dm.cell + dm.px 4) (bx.y + inset) (if mine then nameInk else ink)
  for (bx, e) in l.palette do
    b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) pr pill
    b := emojiAt f b e (bx.x + dm.px 6) (bx.y + inset) 0xF5C542
  return b

/-! ## Hits -/

inductive Hit where
  | pill (emoji : String)
  | palette (emoji : String)
  | row
  deriving BEq

def Box.has (b : Box) (x y : Nat) : Bool := b.x ≤ x && x < b.x + b.w && b.y ≤ y && y < b.y + b.h

/-- What a tap at (x, y) in the row's own pixels lands on. -/
def hit (l : Layout) (x y : Nat) : Hit := Id.run do
  for (bx, e, _, _) in l.pills do
    if bx.has x y then return .pill e
  for (bx, e) in l.palette do
    if bx.has x y then return .palette e
  return .row

end Row
