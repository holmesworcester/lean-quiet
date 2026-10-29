/-
A message row: what it shows (`RowData`, read from live answers), where
each part goes (`layout`, pure), and its pixels (`paint`, pure: it runs
on a worker task, and the frame shows the last finished paint).

Slack-like, on a dark background: the author's avatar, their name in
bold and the time, the text, the pictures (each at its own aspect in a
reserved box, so a picture that decodes late moves nothing; one still
arriving shows its preview with its caption pill inside its box,
Arrival), and the reactions as pills, the user's own outlined. A
selected row also shows the reaction palette. Every part has its own
box, and the boxes do not overlap: what one part paints, no other part
paints over.
-/
import engine.renderer.Paint
import engine.renderer.Scrim
import engine.renderer.Palette
import engine.renderer.Cue
import engine.renderer.Image
import engine.renderer.Text
import engine.renderer.Arrival

namespace Row
open Paint Text Font

/-! ## Theme -/

def bg : Color := Palette.color .dark .bg
def ink : Color := Palette.color .dark .fg
def nameInk : Color := Palette.color .dark .fg
def dim : Color := Palette.color .dark .muted
def pill : Color := Palette.color .dark .selected
def pillMine : Color := Palette.color .dark .tint
def accent : Color := Palette.color .dark .accentInk
def selBg : Color := Palette.color .dark .selected
def placeholder : Color := Palette.color .dark .selected
def twinBg : Color := 0xF06C6C

/-- Sizes for a screen: its density (dpi) and the font's cell. Lengths
are given in dp (Android's density-independent pixels, 160 a inch) and
drawn in pixels; text is the font's cell, about 24 dp. -/
structure Dim where
  dpi : Nat
  cell : Nat
  theme : Theme.Value := .dark
  deriving Inhabited, BEq

def Dim.px (d : Dim) (dp : Nat) : Nat := (dp * d.dpi + 80) / 160
def Dim.pad (d : Dim) : Nat := d.px 12
def Dim.avatar (d : Dim) : Nat := d.px 40
def Dim.textX (d : Dim) : Nat := d.pad + d.avatar + d.px 12
def Dim.lineH (d : Dim) : Nat := d.cell + d.cell / 8
def Dim.topPad (d : Dim) : Nat := d.px 8
def Dim.gap (d : Dim) : Nat := d.px 6
def Dim.pillH (d : Dim) : Nat := d.cell + d.px 8

/-- A picture's caption pill (Arrival): libquiet's sizes, in dp (0.35rem
inset, 0.15rem 0.4rem padding, 0.3rem corners, a 15 ring on a 2.5
stroke), its panel the row's background and its ink the dim ink. -/
def Dim.arrival (d : Dim) : Arrival.Style :=
  { inset := d.px 6, padX := d.px 6, padY := d.px 2, radius := d.px 5,
    ring := d.px 15 / 2, stroke := max 1 (d.px 15 / 6), gap := d.px 4, panel := (Palette.color d.theme .bg), ink := (Palette.color d.theme .muted) }

/-! ## Data -/

/-- A reaction tally: the emoji, how many people, whether one is me. -/
structure Tally where
  emoji : String
  n : Nat
  mine : Bool
  deriving BEq, Inhabited

/-- A picture: an attachment of the message (Kinds.File). Its file's root
(`hash`), its size in pixels and its length in bytes (the sealed file's:
what downloads); its preview, shown until every chunk is here; how many
of its chunks are here (`got`, the engine's count, `Community.progress`)
of `total`; and what opens the file once they all are: the chunks' op ids
in order, the file's key and nonce. -/
structure Pic where
  hash : ByteArray
  w : Nat
  h : Nat
  len : Nat := 0
  preview : ByteArray := .empty
  got : Nat := 0
  total : Nat := 0
  chunks : List ByteArray := []
  key : ByteArray := .empty
  nonce : ByteArray := .empty
  /-- The attachment op's identity, distinct from its shared content hash. -/
  attachment : ByteArray := .empty
  deriving BEq, Inhabited

/-- Whether every chunk is here. -/
def Pic.complete (p : Pic) : Bool := Arrival.done p.got p.total

/-- What a picture shows: the file once every chunk is here and it is
decoded (`full`), else its preview (`pre`; none while either decodes); and
whether that is the file. -/
def Pic.shown {α : Type} (p : Pic) (pre full : Option α) : Option α × Bool :=
  if p.complete then
    match full with
    | some b => (some b, true)
    | none => (pre, false)
  else (pre, false)

structure RowData where
  name : String
  avatar : Option ByteArray
  text : String
  time : Nat
  pics : List Pic
  tallies : List Tally
  pending : Bool
  selected : Bool
  /-- Another user's name looks the same: marked "Duplicate". -/
  namesake : Bool := false
  /-- Identity supplied by the message op; the author component owns its profile. -/
  author : ByteArray := .empty
  /-- The signed root identity. None is a root, including legacy messages. -/
  clump : Option ByteArray := none
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
  /-- The duplicate-name label after the name, when the name has a
  namesake: its box and its line. -/
  twin : Option (Box × Line) := none
  deriving Inhabited

/-- The quick reactions, as libquiet's tray offers them. -/
def quick : Array String := #["👍", "❤️", "😂", "🎉", "👀", "🙏"]

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

/-- The row's pictures and pills below its text (from y), and its height. -/
def layoutBody (f : Font) (dm : Dim) (W : Nat) (d : RowData) (y0 : Nat) :
    Array Box × Array (Box × String × Line × Bool) × Nat := Id.run do
  let tx := dm.textX
  let tw := W - tx - dm.pad
  let mut y := y0
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
  return (pics, pills, max (y + dm.px 8) (dm.topPad + dm.avatar + dm.px 8))

/-- A line moved to start at its box's start edge (its leftmost glyph at
0), in either direction: a right-to-left name or line sits next to the
avatar, not at the far side of its box, as libquiet's rows (no `dir`,
start-aligned) draw it. Its glyphs and their spacing are kept. -/
def flush (l : Line) : Line :=
  match (l.toList.map (·.x)).min? with
  | some m => l.map fun g => { g with x := g.x - m }
  | none => l

/-- Quiet's label for a name another user's looks the same as. -/
def twinText : String := "⚠ Duplicate"

/-- The duplicate label's box, from x on the name's line, and its line. -/
def twinPill (f : Font) (dm : Dim) (x : Nat) : Box × Line :=
  let l := oneLine f (dm.cell * 8) twinText
  (⟨x, dm.topPad - min dm.topPad (dm.px 1), dm.px 6 + Paint.Line.width f l + dm.px 6, f.cell + dm.px 2⟩, l)

/-- The row: its name and time on the first line (each cut as `oneLine`
cuts), its text wrapped below, then its pictures and pills. -/
def layout (f : Font) (dm : Dim) (W : Nat) (d : RowData) : Layout :=
  let tx := dm.textX
  let tw := W - tx - dm.pad
  let lh := dm.lineH
  let name := flush (oneLine f (tw / 2) d.name)
  let nx := tx + Paint.Line.width f name + dm.px 8
  let twin := if d.namesake then some (twinPill f dm nx) else none
  let timeX := match twin with | some (bx, _) => bx.x + bx.w + dm.px 8 | none => nx
  let time := oneLine f (dm.cell * 4) (if d.pending then "pending" else clock d.time)
  let text := if d.text.isEmpty then #[] else (Text.layout f tw d.text).map flush
  let textY := dm.topPad + lh
  let (pics, pills, h) := layoutBody f dm W d (textY + text.size * lh)
  ⟨h, name, time, timeX, text, textY, pics, pills, #[], twin⟩

/-! ## Paint -/

/-- A picture's caption pill in its box (none once the file is here). -/
def arrival (f : Font) (dm : Dim) (bx : Box) (p : Pic) : Option Arrival.Pill :=
  Arrival.layout f dm.arrival bx.x bx.y bx.w bx.h p.got p.total p.len

/-- An emoji (a whole sequence) with its top left at (x, y). -/
def emojiAt (f : Font) (b : Bitmap) (e : String) (x y : Nat) (c : Color) : Bitmap :=
  b.line f (oneLine f (4 * f.cell) e) x y c

/-- The row's pixels: the layout's parts, each in its box. av is the
avatar and imgs the pictures, each at its box's size, or none while it
decodes (a placeholder box is drawn instead). -/
def paint (f : Font) (dm : Dim) (W : Nat) (bgRow : ByteArray) (d : RowData) (l : Layout)
    (av : Option Bitmap) (imgs : Array (Option Bitmap)) : Bitmap := Id.run do
  let mut b := Bitmap.blank W l.h bgRow
  if d.selected then b := b.fill 0 0 W l.h (Palette.color dm.theme .selected)
  let tx := dm.textX
  let lh := dm.lineH
  -- glyphs sit in their line: the cell, then an eighth of it below
  let ay := dm.topPad
  let a := dm.avatar
  match av with
  | some img => b := b.image img dm.pad ay (a / 2)
  | none => b := b.round dm.pad ay (dm.pad + a) (ay + a) (a / 2) (Palette.color dm.theme .selected)
  if d.selected then
    b := b.line f (oneLine f a (Cue.caption dm.theme .selected)) dm.pad ay (Palette.color dm.theme .fg) true
  b := b.line f l.name tx dm.topPad (Palette.color dm.theme .fg) true
  if let some (bx, lbl) := l.twin then
    b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) (dm.px 8) twinBg
    b := b.line f lbl (bx.x + dm.px 6) dm.topPad (Palette.color dm.theme .fg)
  b := b.line f l.time l.timeX dm.topPad (Palette.color dm.theme .muted)
  let tc := if d.pending then (Palette.color dm.theme .muted) else (Palette.color dm.theme .fg)
  for i in [0:l.text.size] do
    b := b.line f l.text[i]! tx (l.textY + i * lh) tc
  let r := dm.px 8
  for i in [0:l.pics.size] do
    let bx := l.pics[i]!
    match imgs[i]? >>= id with
    | some img => b := b.image img bx.x bx.y r
    | none => b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) r (Palette.color dm.theme .selected)
    if let some pl := d.pics[i]? >>= arrival f dm bx then b := Arrival.paint f dm.arrival b pl
  let pr := dm.pillH / 2
  let inset := dm.px 4
  for (bx, e, count, mine) in l.pills do
    if mine then
      b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) pr (Palette.color dm.theme .accentInk)
      let k := max 2 (dm.px 1)
      b := b.round (bx.x + k) (bx.y + k) (bx.x + bx.w - k) (bx.y + bx.h - k) (pr - k) (Palette.color dm.theme .tint)
    else
      b := b.round bx.x bx.y (bx.x + bx.w) (bx.y + bx.h) pr (Palette.color dm.theme .selected)
    b := emojiAt f b e (bx.x + dm.px 10) (bx.y + inset) (Palette.color dm.theme .warning)
    b := b.line f count (bx.x + dm.px 10 + dm.cell + dm.px 4) (bx.y + inset) (if mine then (Palette.color dm.theme .fg) else (Palette.color dm.theme .fg))
  return b

/-- A bitmap darkened to 40%: the rows behind the reaction tray. -/
def Bitmap.dim (b : Bitmap) : Bitmap := Scrim.shade b

/-! ## The reaction tray

A long press on a message opens it: the quick reactions in a bar beside
the message, the rest of the list dimmed. A key the user already holds
is ringed. -/

def trayBg : Color := Palette.color .dark .panel

structure Tray where
  bmp : Bitmap
  keys : Array (Box × String)

def Dim.key (d : Dim) : Nat := d.cell + d.px 16

def tray (f : Font) (dm : Dim) (mine : List String) (backdrop : Color) : Tray := Id.run do
  let k := dm.key
  let p := dm.px 6
  let w := quick.size * k + (quick.size + 1) * p
  let h := k + 2 * p
  let mut b := Bitmap.blank w h (solid backdrop w)
  b := b.round 0 0 w h (h / 2) (Palette.color dm.theme .edge)
  let e := max 2 (dm.px 1)
  b := b.round e e (w - e) (h - e) (h / 2 - e) (Palette.color dm.theme .panel)
  let mut keys := #[]
  for i in [0:quick.size] do
    let q := quick[i]!
    let x := p + i * (k + p)
    if mine.contains q then
      b := b.round x p (x + k) (p + k) (k / 2) (Palette.color dm.theme .accentInk)
      b := b.round (x + e) (p + e) (x + k - e) (p + k - e) (k / 2 - e) (Palette.color dm.theme .tint)
    let ew := Paint.Line.width f (oneLine f (4 * f.cell) q)
    b := emojiAt f b q (x + (k - ew) / 2) (p + (k - f.cell) / 2) (Palette.color dm.theme .fg)
    keys := keys.push (⟨x, p, k, k⟩, q)
  return ⟨b, keys⟩

/-! ## Hits -/

inductive Hit where
  | pill (emoji : String)
  | palette (emoji : String)
  /-- The duplicate-name label. -/
  | twin
  | row
  deriving BEq

def Box.has (b : Box) (x y : Nat) : Bool := b.x ≤ x && x < b.x + b.w && b.y ≤ y && y < b.y + b.h

/-- What a tap at (x, y) in the row's own pixels lands on. -/
def hit (l : Layout) (x y : Nat) : Hit := Id.run do
  if let some (bx, _) := l.twin then
    if bx.has x y then return .twin
  for (bx, e, _, _) in l.pills do
    if bx.has x y then return .pill e
  for (bx, e) in l.palette do
    if bx.has x y then return .palette e
  return .row

end Row
