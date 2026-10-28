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

def pad : Nat := 32
def avatar : Nat := 80
def textX : Nat := pad + avatar + 24
def lineH : Nat := 40
def topPad : Nat := 16

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

/-- The picture's box: at most 600 x 480 and the text's width, its
aspect kept. -/
def picBox (maxW : Nat) (p : Pic) : Nat × Nat :=
  let mw := min 600 maxW
  let mh := 480
  let w := max p.w 1
  let h := max p.h 1
  if w * mh ≤ h * mw then (max 1 (w * mh / h), mh) else (mw, max 1 (h * mw / w))

def layout (f : Font) (W : Nat) (d : RowData) : Layout := Id.run do
  let tw := W - textX - pad
  let name := oneLine f (tw / 2) d.name
  let timeX := textX + Paint.Line.width f name + 16
  let time := oneLine f 200 (if d.pending then "pending" else clock d.time)
  let text := if d.text.isEmpty then #[] else Text.layout f tw d.text
  let mut y := topPad + 4 + lineH
  let textY := y
  y := y + text.size * lineH
  let mut pics := #[]
  for p in d.pics do
    y := y + 12
    let (w, h) := picBox tw p
    pics := pics.push ⟨textX, y, w, h⟩
    y := y + h
  let mut pills := #[]
  let mut x := textX
  if !d.tallies.isEmpty then y := y + 12
  for t in d.tallies do
    let count := oneLine f 80 (toString t.n)
    let w := 24 + 32 + 8 + Paint.Line.width f count + 20
    if x + w > W - pad then x := textX; y := y + 56
    pills := pills.push (⟨x, y, w, 48⟩, t.emoji, count, t.mine)
    x := x + w + 12
  if !d.tallies.isEmpty then y := y + 48
  let mut palette := #[]
  if d.selected then
    y := y + 16
    let mut px := textX
    for e in emojiPalette do
      palette := palette.push (⟨px, y, 80, 64⟩, e)
      px := px + 92
    y := y + 64
  let h := max (y + 16) (topPad + avatar + 16)
  return ⟨h, name, time, timeX, text, textY, pics, pills, palette⟩

/-! ## Paint -/

/-- An emoji's glyph centred in a box (its first code point). -/
def emojiAt (f : Font) (b : Bitmap) (e : String) (x y : Nat) (c : Color) : Bitmap :=
  b.glyph f (e.toList.headD ' ').val x y c false

/-- The row's pixels: the layout's parts, each in its box. imgs holds the
avatar (index 0) and the pictures, each at its box's size, or none while
it decodes (a placeholder box is drawn instead). -/
def paint (f : Font) (W : Nat) (bgRow : ByteArray) (d : RowData) (l : Layout)
    (av : Option Bitmap) (imgs : Array (Option Bitmap)) : Bitmap := Id.run do
  let mut b := Bitmap.blank W l.h bgRow
  if d.selected then b := b.fill 0 0 W l.h selBg
  -- avatar
  let ay := topPad
  match av with
  | some a => b := b.image a pad ay (avatar / 2)
  | none => b := b.round pad ay (pad + avatar) (ay + avatar) (avatar / 2) placeholder
  -- name and time
  b := b.line f l.name textX (topPad + 4) nameInk true
  b := b.line f l.time l.timeX (topPad + 4) dim
  -- text
  let tc := if d.pending then dim else ink
  for i in [0:l.text.size] do
    b := b.line f l.text[i]! textX (l.textY + i * lineH) tc
  -- pictures
  for i in [0:l.pics.size] do
    let bx := l.pics[i]!
    match imgs[i]? >>= id with
    | some img => b := b.image img bx.x bx.y 12
    | none => b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) 12 placeholder
  -- reactions
  for (bx, e, count, mine) in l.pills do
    if mine then
      b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) 24 accent
      b := b.round (bx.x + 3) (bx.y + 3) (bx.x + bx.w - 3) (bx.y + bx.h - 3) 21 pillMine
    else
      b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) 24 pill
    b := emojiAt f b e (bx.x + 24) (bx.y + 8) 0xF5C542
    b := b.line f count (bx.x + 24 + 32 + 8) (bx.y + 8) (if mine then nameInk else ink)
  -- palette
  for (bx, e) in l.palette do
    b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) 20 pill
    b := emojiAt f b e (bx.x + 24) (bx.y + 16) 0xF5C542
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
