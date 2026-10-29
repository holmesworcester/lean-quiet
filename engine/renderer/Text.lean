/-
Text to placed glyphs: a light shaper, line wrapping, and paragraph bidi.

- **Shaping.** Arabic letters take their contextual form (isolated,
  final, initial or medial) from Unicode's presentation forms, by their
  joining type; marks (combining accents, Thai vowels, Hebrew points,
  Arabic harakat) have no advance and sit on the glyph before them;
  joiners and variation selectors draw nothing.
- **Wrapping.** Lines break at spaces, between any two wide characters
  (CJK breaks anywhere), at a newline, and inside a word too long for a
  line.
- **Bidi.** Unicode 16.0.0 P2–P3, W1–W7, N1–N2, I1–I2, L1–L2 for
  a line without embeddings, isolates or paired brackets. Maximal EN/AN
  runs remain contiguous in logical order (`numbers_keep_order`,
  `arabic_numbers_keep_order`); display is a permutation (`visual_perm`).
  Directional controls are ON under Quiet's policy. Internal emoji
  tokens are ON too. See docs/BIDI.md for the audit and limits.

Not handled: scripts that reorder or stack (Devanagari and other Indic
scripts), ligatures, and emoji sequences absent from the emoji asset.
-/
import engine.renderer.Font
import engine.renderer.Chars
import engine.renderer.bidi.Basic

namespace Text
open Font

/-- A glyph placed on a line: its code point and x (from the line's start). -/
structure Placed where
  c : UInt32
  x : Nat
  deriving Inhabited

abbrev Line := Array Placed

/-- Digits (European, Arabic-Indic, extended Arabic-Indic): weak, they
keep their left-to-right order inside right-to-left text. -/
def isDigit (c : UInt32) : Bool :=
  inRange c 0x30 0x39 || inRange c 0x0660 0x0669 || inRange c 0x06F0 0x06F9

def isRtl (c : UInt32) : Bool :=
  (inRange c 0x0590 0x05FF || inRange c 0x0600 0x06FF || inRange c 0xFB1D 0xFDFF ||
   inRange c 0xFE70 0xFEFF) && !isDigit c

def isStrongLtr (c : UInt32) : Bool :=
  (inRange c 0x41 0x5A || inRange c 0x61 0x7A || inRange c 0xC0 0x24F || inRange c 0x370 0x58F ||
   inRange c 0x10A0 0x10FF || inRange c 0x0E00 0x0E7F || inRange c 0x3040 0x9FFF ||
   inRange c 0xAC00 0xD7AF) && !isMark c

/-! ## Arabic forms -/

/-- An Arabic letter's first presentation form (isolated; then final,
initial, medial) and whether it joins on both sides (dual) or only to
the letter before (right-joining). -/
def arabic (c : UInt32) : Option (UInt32 × Bool) :=
  match c with
  | 0x0621 => some (0xFE80, false) | 0x0622 => some (0xFE81, false) | 0x0623 => some (0xFE83, false)
  | 0x0624 => some (0xFE85, false) | 0x0625 => some (0xFE87, false) | 0x0626 => some (0xFE89, true)
  | 0x0627 => some (0xFE8D, false) | 0x0628 => some (0xFE8F, true) | 0x0629 => some (0xFE93, false)
  | 0x062A => some (0xFE95, true) | 0x062B => some (0xFE99, true) | 0x062C => some (0xFE9D, true)
  | 0x062D => some (0xFEA1, true) | 0x062E => some (0xFEA5, true) | 0x062F => some (0xFEA9, false)
  | 0x0630 => some (0xFEAB, false) | 0x0631 => some (0xFEAD, false) | 0x0632 => some (0xFEAF, false)
  | 0x0633 => some (0xFEB1, true) | 0x0634 => some (0xFEB5, true) | 0x0635 => some (0xFEB9, true)
  | 0x0636 => some (0xFEBD, true) | 0x0637 => some (0xFEC1, true) | 0x0638 => some (0xFEC5, true)
  | 0x0639 => some (0xFEC9, true) | 0x063A => some (0xFECD, true) | 0x0641 => some (0xFED1, true)
  | 0x0642 => some (0xFED5, true) | 0x0643 => some (0xFED9, true) | 0x0644 => some (0xFEDD, true)
  | 0x0645 => some (0xFEE1, true) | 0x0646 => some (0xFEE5, true) | 0x0647 => some (0xFEE9, true)
  | 0x0648 => some (0xFEED, false) | 0x0649 => some (0xFEEF, false) | 0x064A => some (0xFEF1, true)
  | _ => none

/-- The contextual forms of a run of code points. -/
def shape (cs : Array UInt32) : Array UInt32 := Id.run do
  -- the letter before and after each position, skipping marks
  let n := cs.size
  let mut out := cs
  for i in [0:n] do
    if let some (base, dual) := arabic cs[i]! then
      let mut j := i
      let mut prevDual := false
      while j > 0 do
        j := j - 1
        if isMark cs[j]! then continue
        prevDual := (arabic cs[j]!).any (·.2)
        break
      let mut k := i + 1
      let mut nextJoins := false
      while k < n do
        if isMark cs[k]! then k := k + 1; continue
        nextJoins := (arabic cs[k]!).isSome
        break
      let joinNext := dual && nextJoins
      let form : UInt32 :=
        if base == 0xFE80 then 0
        else if prevDual && joinNext then 3
        else if prevDual then 1
        else if joinNext then 2
        else 0
      out := out.set! i (base + form)
  return out

/-! ## Wrapping -/

def isSpace (c : UInt32) : Bool := c == 32 || c == 9

/-- The advance of code point c in the font. -/
def adv (f : Font) (c : UInt32) : Nat :=
  if Emoji.isEmoji c then f.emoji.scale f.cell (f.emoji.width c)
  else if isMark c || isInvisible c then 0 else f.adv (f.glyph c)

/-- Wide characters (CJK, emoji) are words of their own for wrapping. -/
def wide (f : Font) (c : UInt32) : Bool := Emoji.isEmoji c || adv f c == f.cell

/-- The longest prefix whose elements satisfy p, and the rest. -/
def splitW {α : Type} (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | x :: t => if p x then let r := splitW p t; (x :: r.1, r.2) else ([], x :: t)

theorem splitW_append {α : Type} (p : α → Bool) : ∀ l : List α, (splitW p l).1 ++ (splitW p l).2 = l
  | [] => rfl
  | x :: t => by unfold splitW; split <;> simp [splitW_append p t]

theorem splitW_len {α : Type} (p : α → Bool) : ∀ l : List α, (splitW p l).2.length ≤ l.length
  | [] => by simp [splitW]
  | x :: t => by unfold splitW; split <;> simp; have := splitW_len p t; omega

/-- A paragraph's tokens: each space alone; a wide character (CJK, emoji)
with the zero-advance characters after it (its marks); a run of other
characters (a word). -/
def tokens (f : Font) : List UInt32 → List (List UInt32)
  | [] => []
  | c :: t =>
    if isSpace c then [c] :: tokens f t
    else if wide f c then
      let r := splitW (fun d => adv f d == 0) t
      (c :: r.1) :: tokens f r.2
    else
      let r := splitW (fun d => !isSpace d && !wide f d) t
      (c :: r.1) :: tokens f r.2
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals
    have h1 := splitW_len (fun d => adv f d == 0) t
    have h2 := splitW_len (fun d => !isSpace d && !wide f d) t
    omega

/-- A line's width. -/
def lineW (f : Font) (l : List UInt32) : Nat := (l.map (adv f)).sum

/-- A line without its trailing spaces. -/
def trimEnd (l : List UInt32) : List UInt32 := (l.reverse.dropWhile isSpace).reverse

/-- A word longer than a line, broken inside it: each character on the
current line if it fits (or the line is empty), else on a new one. -/
def breakIn (f : Font) (width : Nat) : List UInt32 → List (List UInt32) → List UInt32 →
    List (List UInt32) × List UInt32
  | [], lines, cur => (lines, cur)
  | c :: t, lines, cur =>
    if lineW f cur + adv f c > width && !cur.isEmpty then breakIn f width t (lines ++ [trimEnd cur]) [c]
    else breakIn f width t lines (cur ++ [c])

/-- Tokens onto lines of at most `width` pixels: a space joins the line; a
token that fits joins it; one that fits a line starts a new one (the old
line's trailing spaces dropped); one longer than a line is broken. -/
def fill (f : Font) (width : Nat) : List (List UInt32) → List (List UInt32) → List UInt32 → List (List UInt32)
  | [], lines, cur => lines ++ [trimEnd cur]
  | tok :: t, lines, cur =>
    if tok.all isSpace then fill f width t lines (cur ++ tok)
    else if lineW f cur + lineW f tok ≤ width then fill f width t lines (cur ++ tok)
    else if lineW f tok ≤ width then fill f width t (lines ++ [trimEnd cur]) tok
    else let r := breakIn f width tok lines cur; fill f width t r.1 r.2

/-- Paragraphs (split at newlines) into lines of at most `width` pixels,
as code points in logical order. Laws (TextLaws): `wrap_keeps` (only
spaces are dropped, nothing else is lost, added or reordered) and
`wrap_fits` (every line fits, when every character does). -/
def wrapL (f : Font) (width : Nat) (cs : List UInt32) : List (List UInt32) :=
  fill f width (tokens f cs) [] []

def wrapPara (f : Font) (width : Nat) (cs : Array UInt32) : Array (Array UInt32) :=
  ((wrapL f width cs.toList).map List.toArray).toArray

/-! ## Bidi and placing -/

/-- The Unicode 16 class, with Quiet's neutral-control policy. -/
def dirOf (c : UInt32) : Bidi.Class :=
  if Emoji.isEmoji c then .on else Bidi.dirOf c

/-- P2–P3 on the logical line. -/
def rtlPara (cs : List UInt32) : Bool := Bidi.paragraph (cs.map dirOf)

def levels (cs : List UInt32) : List Nat :=
  Bidi.levels (rtlPara cs) (cs.map fun c => (c, dirOf c))

/-- The running display path, with an explicit paragraph direction for
callers that already know it (and the Unicode conformance harness). -/
def visualIn (rtl : Bool) (cs : List UInt32) : List UInt32 :=
  Bidi.display rtl (cs.map fun c => (c, dirOf c))

def visualL (cs : List UInt32) : List UInt32 × Bool :=
  (visualIn (rtlPara cs) cs, rtlPara cs)

def visual (cs : Array UInt32) : Array UInt32 × Bool :=
  let (v, r) := visualL cs.toList
  (v.toArray, r)

/-- A display-order line's glyphs placed from x (the last base at
lastX); a mark sits on the glyph before it (after it, in a reversed run,
where its base now follows it); invisibles are left out. -/
def placeL (f : Font) : List UInt32 → Nat → Nat → List Placed × Nat
  | [], x, _ => ([], x)
  | c :: t, x, lastX =>
    if isInvisible c then placeL f t x lastX
    else if isMark c then
      -- in a reversed run the base is the next non-mark glyph
      let base := if !t.isEmpty && isRtl c then x else lastX
      let (r, w) := placeL f t x lastX
      (⟨c, base⟩ :: r, w)
    else
      let (r, w) := placeL f t (x + adv f c) x
      (⟨c, x⟩ :: r, w)

def place (f : Font) (cs : Array UInt32) : Line × Nat :=
  let (l, w) := placeL f cs.toList 0 0
  (l.toArray, w)

/-- Laid-out text: each line's glyphs and its x offset (right-aligned
right-to-left lines), within `width`. -/
def layout (f : Font) (width : Nat) (s : String) : Array Line := Id.run do
  let paras := s.splitOn "\n"
  let mut out : Array Line := #[]
  for p in paras do
    let cs := shape (f.emoji.emojify (p.toList.toArray.map (·.val)))
    for l in wrapPara f width cs do
      let (vis, rtl) := visual l
      let (placed, w) := place f vis
      let dx := if rtl && w < width then width - w else 0
      out := out.push (placed.map fun g => { g with x := g.x + dx })
  return out

/-- How many characters of `cs`, from its logical start, fit `w` pixels. -/
def fitting (f : Font) (w : Nat) (cs : List UInt32) : Nat := Id.run do
  let mut x := 0
  let mut k := 0
  for c in cs do
    let a := if isMark c || isInvisible c then 0 else adv f c
    if x + a > w then return k
    x := x + a
    k := k + 1
  return k

/-- A single line, cut to `width` with an ellipsis when longer: its
logical start (what a reader of either direction reads first), then the
ellipsis where reading continues (at the right of a left-to-right line,
the left of a right-to-left one: the ellipsis is a neutral at the line's
end, and bidi places it). A right-to-left line sits at the right edge. -/
def cutTo (f : Font) (width : Nat) (cs : Array UInt32) : Array UInt32 :=
  (cs.extract 0 (fitting f (width - min width (adv f 0x2026)) cs.toList)).push 0x2026

/-- What a single line places: the text, or its cut when it is too wide. -/
def oneLinePlaced (f : Font) (width : Nat) (cs : Array UInt32) : Line × Nat :=
  let (placed, w) := place f (visual cs).1
  if w ≤ width then (placed, w) else place f (visual (cutTo f width cs)).1

def oneLine (f : Font) (width : Nat) (s : String) : Line :=
  let cs := shape (f.emoji.emojify (s.toList.toArray.map (·.val)))
  let (placed, w) := oneLinePlaced f width cs
  let dx := if (visual cs).2 && w < width then width - w else 0
  placed.map fun g => { g with x := g.x + dx }

/-- The largest metric width whose final nearest-pixel advance fits. -/
def metricWidth (width : Nat) : Nat := width * 64 + 31

theorem metricWidth_fits (width advance : Nat) (h : advance ≤ metricWidth width) :
    (advance + 32) / 64 ≤ width := by
  unfold metricWidth at h
  omega

/-- Keep 1/64 pixel advances through wrapping and bidi. Round a glyph's
final origin once, instead of rounding each advance and accumulating the
error along a line. This font shares its metric index and never paints. -/
def metricFont (f : Font) : Font := { f with cell := f.cell * 64, fineMetrics := true }

def pixelLine (line : Line) : Line := line.map fun g => { g with x := (g.x + 32) / 64 }

def layoutFine (f : Font) (width : Nat) (s : String) : Array Line :=
  (layout (metricFont f) (metricWidth width) s).map pixelLine

def oneLineFine (f : Font) (width : Nat) (s : String) : Line :=
  pixelLine (oneLine (metricFont f) (metricWidth width) s)

/-- Rounding positions preserves every shaped glyph and its visual order. -/
theorem pixelLine_glyphs (line : Line) :
    (pixelLine line).toList.map (·.c) = line.toList.map (·.c) := by
  simp [pixelLine, Function.comp_def]

end Text
