/-
What has arrived of a picture, drawn over it until all of it has
(libquiet's Attachment.svelte): the preview stands in, softened; a
caption pill sits at the picture's bottom left, the library's ring, then
`arrival`'s words, "42% of 2.0 MiB". The pill is inside the picture's
box, so it adds no line that would disappear when the file lands.

Everything here is a function of what the engine counts: `got` of
`total` chunks (`Community.progress`, one count of the file's Valid
chunk list) and the file's length. The ring is determinate: lit
clockwise from 12 o'clock over got/total of a turn, on its track (the
ink at 10%). It does not turn: a row is painted once per change of what
it shows, and a turning ring would repaint every arriving row each frame.

The laws (ArrivalLaws) are about these functions, which Row.paint calls.
-/
import engine.renderer.Paint

namespace Arrival
open Paint Font Text

/-! ## Words -/

/-- libquiet's `humanBytes`: bytes below a KiB, then KiB, MiB or GiB, with
one decimal below ten (rounded half up, as `toFixed(1)`) and none above
(as `Math.round`). -/
def humanBytes (n : Nat) : String :=
  if n < 1024 then s!"{n} B" else
  let (u, unit) := if n < 1024 ^ 2 then (1024, "KiB") else if n < 1024 ^ 3 then (1024 ^ 2, "MiB")
    else (1024 ^ 3, "GiB")
  if n < 10 * u then
    let t := (10 * n + u / 2) / u
    s!"{t / 10}.{t % 10} {unit}"
  else s!"{(n + u / 2) / u} {unit}"

/-- Whether all of the file is here: every one of its chunks. -/
def done (got total : Nat) : Bool := total > 0 && got ≥ total

/-- How much of the file is here, in whole percent (floored). -/
def percent (got total : Nat) : Nat := 100 * got / total

/-- libquiet's `arrival`, for a picture: until the file is here, how much
of it is; nothing once it is. -/
def caption (got total len : Nat) : Option String :=
  if done got total then none else some s!"{percent got total}% of {humanBytes len}"

/-! ## The ring

The ring's square has side 2R. Pixel (i, j) of it (j down) is taken at
its centre, as doubled offsets from the square's centre: `off R i`
across and `off R j` up or down. Both are odd, so no pixel's centre is
the ring's, and every pixel has a direction. -/

/-- A pixel's doubled distance from the centre line, in one axis. -/
def off (R i : Nat) : Nat := if R ≤ i then 2 * (i - R) + 1 else 2 * (R - i) - 1

/-- Whether pixel (i, j) is on the ring: in the square, its centre between
the circle of radius R and the one of radius R - s. -/
def onRing (R s i j : Nat) : Bool :=
  let d2 := off R i * off R i + off R j * off R j
  i < 2 * R && j < 2 * R && 4 * ((R - s) * (R - s)) ≤ d2 && d2 ≤ 4 * (R * R)

/-- How far clockwise from 12 o'clock pixel (i, j) sits, in quarter turns,
as an exact fraction n / m: the quarter it is in, and how far across it
(the "diamond angle", the angle's monotone stand-in, equal to it at every
eighth of a turn and within 5° of it between). -/
def turn (R i j : Nat) : Nat × Nat :=
  let u := off R i
  let v := off R j
  let m := u + v
  if R ≤ i then
    if j < R then (u, m) else (m + v, m)
  else
    if j < R then (3 * m + v, m) else (2 * m + u, m)

/-- Whether pixel (i, j)'s direction is within the arc of got/total of a
turn, clockwise from 12 o'clock: turn < 4 · got / total, in integers. -/
def arc (R got total i j : Nat) : Bool :=
  let (n, m) := turn R i j
  n * total < 4 * got * m

/-- The ring's lit pixels: on the ring and within the arc. -/
def lit (R s got total i j : Nat) : Bool := onRing R s i j && arc R got total i j

/-- The ring with its square's top left at (x, y): its lit pixels in c,
the rest of it the track. -/
def paintRing (b : Bitmap) (R s got total x y : Nat) (c track : Color) : Bitmap := Id.run do
  let mut b := b
  for j in [0:2 * R] do
    b := b.modify (y + j) fun row => Id.run do
      let mut row := row
      for i in [0:2 * R] do
        if onRing R s i j then row := setPx row (x + i) (if arc R got total i j then c else track)
      return row
  return b

/-! ## The pill -/

/-- Its sizes, in pixels, and colours: libquiet's `.attachment
figcaption` and `.draft-wait` (Row.Dim.arrival gives them for a screen). -/
structure Style where
  /-- From the picture's left and bottom edges. -/
  inset : Nat
  padX : Nat
  padY : Nat
  /-- The panel's corners. -/
  radius : Nat
  /-- The ring's radius and stroke. -/
  ring : Nat
  stroke : Nat
  /-- Between the ring and the words. -/
  gap : Nat
  panel : Color
  ink : Color

/-- Its width without the words', the insets included. -/
def Style.fixed (z : Style) : Nat := 2 * z.inset + 2 * z.padX + 2 * z.ring + z.gap

/-- Its height: the taller of a line and the ring, padded. -/
def Style.height (z : Style) (f : Font) : Nat := max f.cell (2 * z.ring) + 2 * z.padY

/-- The track: the ink at 10% over the panel. -/
def Style.track (z : Style) : Color := mixC z.panel z.ink 26

/-- A pill as placed: its panel's box, the ring's square's top left, the
words and their line's top left, and the counts it shows. -/
structure Pill where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  rx : Nat
  ry : Nat
  words : String
  line : Line
  tx : Nat
  ty : Nat
  got : Nat
  total : Nat
  deriving Inhabited

/-- The words, laid out at most the box's width, if the pill with them
fits the box's width. -/
def fit (f : Font) (z : Style) (bw : Nat) (s : String) : Option (String × Line) :=
  let l := oneLine f bw s
  if z.fixed + Line.width f l ≤ bw then some (s, l) else none

/-- The pill over a picture whose box is (bx, by, bw, bh), for got of total
chunks of a len-byte file: none once the file is here. It sits `inset`
from the box's bottom left and holds the ring, then the caption's words
if they fit the box, else the percent alone; none in a box too small for
even that. -/
def layout (f : Font) (z : Style) (bx by_ bw bh got total len : Nat) : Option Pill :=
  match caption got total len with
  | none => none
  | some words =>
    match fit f z bw words <|> fit f z bw s!"{percent got total}%" with
    | none => none
    | some (s, l) =>
      let h := z.height f
      if 2 * z.inset + h ≤ bh then
        let x := bx + z.inset
        let y := by_ + bh - z.inset - h
        some { x, y, w := 2 * z.padX + 2 * z.ring + z.gap + Line.width f l, h,
               rx := x + z.padX, ry := y + (h - 2 * z.ring) / 2, words := s, line := l,
               tx := x + z.padX + 2 * z.ring + z.gap, ty := y + (h - f.cell) / 2, got, total }
      else none

/-- The pill's pixels over b: its panel, the ring, the words. -/
def paint (f : Font) (z : Style) (b : Bitmap) (p : Pill) : Bitmap :=
  let b := b.round p.x p.y (p.x + p.w) (p.y + p.h) z.radius z.panel
  let b := paintRing b z.ring z.stroke p.got p.total p.rx p.ry z.ink z.track
  b.line f p.line p.tx p.ty z.ink

/-! ## The preview -/

/-- The preview, softened as libquiet's `.attachment-partial` softens it
(so the swap to the file reads as it arriving): saturation 0.85, then
0.75 opaque over bg. -/
def soften (bg : Color) (b : Bitmap) : Bitmap :=
  { b with rows := b.rows.map fun row => Id.run do
      let mut out := row
      for k in [0:row.size / 4] do
        let i := 4 * k
        let (r, g, bl) := (row[i]!.toNat, row[i+1]!.toNat, row[i+2]!.toNat)
        let l := (54 * r + 183 * g + 19 * bl) / 256
        let ch (c under : Nat) : UInt8 := ((3 * ((85 * c + 15 * l) / 100) + under) / 4).toUInt8
        out := ((out.set! i (ch r (r8 bg).toNat)).set! (i + 1) (ch g (g8 bg).toNat)).set! (i + 2) (ch bl (b8 bg).toNat)
      return out }

end Arrival
