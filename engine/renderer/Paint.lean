/-
Pixels. A bitmap is an array of pixel rows, 4 bytes a pixel (R G B X),
the form the platform's frames take. Painting writes rows in place: a
row that nothing touches stays the one shared background row, so a
bitmap of mostly background costs one row of memory, and the twin never
copies a row it already holds.
-/
import engine.renderer.Font
import engine.renderer.Text

namespace Paint
open Font Text

abbrev Color := UInt32

def r8 (c : Color) : UInt8 := (c >>> 16).toUInt8
def g8 (c : Color) : UInt8 := (c >>> 8).toUInt8
def b8 (c : Color) : UInt8 := c.toUInt8

/-- One row of w pixels of colour c. -/
def solid (c : Color) (w : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * w)
  for _ in [0:w] do
    b := b.push (r8 c) |>.push (g8 c) |>.push (b8 c) |>.push 255
  return b

structure Bitmap where
  w : Nat
  rows : Array ByteArray
  deriving Inhabited

def Bitmap.h (b : Bitmap) : Nat := b.rows.size

/-- h rows of the given background row (one shared object). -/
def Bitmap.blank (w h : Nat) (bg : ByteArray) : Bitmap := ⟨w, Array.replicate h bg⟩

@[inline] def setPx (row : ByteArray) (x : Nat) (c : Color) : ByteArray :=
  let i := 4 * x
  if i + 3 < row.size then
    ((row.set! i (r8 c)).set! (i + 1) (g8 c)).set! (i + 2) (b8 c)
  else row

/-- a over b by t (0..256), per channel. -/
@[inline] def mixC (a b : Color) (t : Nat) : Color :=
  let ch (s : UInt32) := (((a >>> s) &&& 255).toNat * (256 - t) + ((b >>> s) &&& 255).toNat * t) / 256
  ((ch 16).toUInt32 <<< 16) ||| ((ch 8).toUInt32 <<< 8) ||| (ch 0).toUInt32

@[inline] def getPx (row : ByteArray) (x : Nat) : Color :=
  let i := 4 * x
  if i + 3 < row.size then
    (row[i]!.toUInt32 <<< 16) ||| (row[i+1]!.toUInt32 <<< 8) ||| row[i+2]!.toUInt32
  else 0

/-- Row y, changed by f (in place when the row is not shared). -/
@[inline] def Bitmap.modify (b : Bitmap) (y : Nat) (f : ByteArray → ByteArray) : Bitmap :=
  if y < b.rows.size then { b with rows := b.rows.modify y f } else b

/-- A rectangle of colour c, clipped to the bitmap. -/
def Bitmap.fill (b : Bitmap) (x0 y0 x1 y1 : Nat) (c : Color) : Bitmap := Id.run do
  let x1 := min x1 b.w
  if x0 ≥ x1 then return b
  let src := solid c (x1 - x0)
  let mut b := b
  for y in [y0:min y1 b.h] do
    b := b.modify y fun row => src.copySlice 0 row (4 * x0) (4 * (x1 - x0))
  return b

/-- How much of pixel (x, y) a box with corners of radius r covers, in
256ths (antialiased at the corners only). -/
@[inline] def cover (x0 y0 x1 y1 r x y : Nat) : Nat :=
  let cx := if x < x0 + r then x0 + r else if x ≥ x1 - r then x1 - r - 1 else x
  let cy := if y < y0 + r then y0 + r else if y ≥ y1 - r then y1 - r - 1 else y
  if cx == x || cy == y then 256 else
  -- distance from the corner's centre, in 16ths of a pixel
  let dx := (if x > cx then x - cx else cx - x) * 16 + 8
  let dy := (if y > cy then y - cy else cy - y) * 16 + 8
  let d2 := dx * dx + dy * dy
  let rr := r * 16
  if d2 ≤ (rr - 8) * (rr - 8) then 256
  else if d2 ≥ (rr + 8) * (rr + 8) then 0
  else
    -- linear in distance across the one-pixel edge
    let d := Nat.sqrt d2
    (rr + 8 - d) * 16

/-- A box with rounded corners of radius r, over what is there. -/
def Bitmap.round (b : Bitmap) (x0 y0 x1 y1 r : Nat) (c : Color) : Bitmap := Id.run do
  let r := min r (min ((x1 - x0) / 2) ((y1 - y0) / 2))
  -- the middle band and the straight parts of the corner rows are fills
  let mut b := b.fill x0 (y0 + r) x1 (y1 - r) c
  for y in (List.range' y0 r ++ List.range' (y1 - r) r) do
    b := b.modify y fun row => Id.run do
      let mut row := (solid c (x1 - x0 - 2 * r)).copySlice 0 row (4 * (x0 + r)) (4 * (x1 - x0 - 2 * r))
      for x in (List.range' x0 r ++ List.range' (x1 - r) r) do
        let t := cover x0 y0 x1 y1 r x y
        if t > 0 then row := setPx row x (mixC (getPx row x) c t)
      return row
  return b

/-- Emoji code point ch's picture with its top left at (x, y), laid over
what is there by its alpha. -/
def Bitmap.emoji (f : Font) (b : Bitmap) (ch : UInt32) (x y : Nat) : Bitmap := Id.run do
  let some q := f.emoji.picture ch | return b
  let w := q.w.toNat
  let mut b := b
  for r in [0:q.h.toNat] do
    b := b.modify (y + r) fun row => Id.run do
      let mut row := row
      for i in [0:w] do
        let p := q.px[r * w + i]!
        let a := (p &&& 255).toNat
        if a == 0 then continue
        let src : Color := ((p >>> 24) <<< 16) ||| (((p >>> 16) &&& 255) <<< 8) ||| ((p >>> 8) &&& 255)
        row := setPx row (x + i) (if a == 255 then src else mixC (getPx row (x + i)) src (a * 256 / 255))
      return row
  return b

/-- The glyph of code point ch with its top left at (x, y), in colour
c; bold smears each row right. -/
def Bitmap.glyph (f : Font) (b : Bitmap) (ch : UInt32) (x y : Nat) (c : Color) (bold : Bool) : Bitmap := Id.run do
  if Emoji.isEmoji ch then return b.emoji f ch x y
  let g := f.glyph ch
  let n := f.adv g
  -- bold smears each row right by a sixteenth of the cell
  let smear := if bold then max 1 (f.cell / 32) else 0
  let mut b := b
  for r in [0:f.cell] do
    let bits0 := f.row g r
    let mut bits := bits0
    for k in [1:smear + 1] do bits := bits ||| (bits0 >>> k.toUInt64)
    if bits == 0 then continue
    b := b.modify (y + r) fun row => Id.run do
      let mut row := row
      for i in [0:min 64 (n + smear)] do
        if bits &&& (0x8000000000000000 >>> i.toUInt64) != 0 then row := setPx row (x + i) c
      return row
  return b

/-- A laid-out line at (x, y). -/
def Bitmap.line (f : Font) (b : Bitmap) (l : Line) (x y : Nat) (c : Color) (bold := false) : Bitmap :=
  l.foldl (fun b g => b.glyph f g.c (x + g.x) y c bold) b

/-- The width a line's glyphs take. -/
def Line.width (f : Font) (l : Line) : Nat := l.foldl (fun w g => max w (g.x + adv f g.c)) 0

/-- An image's rows (already at their drawn size) at (x, y), with corners
of radius r rounded onto what is there (r = w/2 for a circle). -/
def Bitmap.image (b : Bitmap) (img : Bitmap) (x y r : Nat) : Bitmap := Id.run do
  let w := min img.w (b.w - min x b.w)
  if w == 0 then return b
  let mut b := b
  for i in [0:img.h] do
    let src := img.rows[i]!
    b := b.modify (y + i) fun row => Id.run do
      if r == 0 || (i ≥ r && i + r < img.h) then
        return src.copySlice 0 row (4 * x) (4 * w)
      let mut row := row
      for j in [0:w] do
        let t := cover 0 0 img.w img.h r j i
        if t == 256 then row := setPx row (x + j) (getPx src j)
        else if t > 0 then row := setPx row (x + j) (mixC (getPx row (x + j)) (getPx src j) t)
      return row
  return b

end Paint
