/-
Text to placed glyphs: a light shaper, line wrapping, and a light bidi.

- **Shaping.** Arabic letters take their contextual form (isolated,
  final, initial or medial) from Unicode's presentation forms, by their
  joining type; marks (combining accents, Thai vowels, Hebrew points,
  Arabic harakat) have no advance and sit on the glyph before them;
  joiners and variation selectors draw nothing.
- **Wrapping.** Lines break at spaces, between any two wide characters
  (CJK breaks anywhere), at a newline, and inside a word too long for a
  line.
- **Bidi.** Unicode's bidi algorithm for one paragraph without explicit
  embeddings (`levels`, `reorder`): right-to-left letters at level 1,
  left-to-right text and digits inside right-to-left text embedded at 2
  (so a number keeps its order), neutrals as their neighbours agree, and
  rule L2's reversals. A line whose first strong character is
  right-to-left sits at the right edge. Bidi controls are neutrals: they
  reorder nothing.

Not handled: scripts that reorder or stack (Devanagari and other Indic
scripts), ligatures, and emoji sequences (ZWJ, skin tones), which draw
their parts.
-/
import engine.renderer.Font
import engine.renderer.Chars

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
  if Emoji.isEmoji c then f.emoji.width c
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

/-- A character's bidi class, as this light bidi resolves it: strong
right-to-left, strong left-to-right, a digit (weak), or neutral (spaces,
punctuation, symbols, emoji, and every control: an explicit bidi control
is a neutral here, so it cannot reorder anything). -/
inductive Dir where
  | r | l | en | n
  deriving BEq, Inhabited, Repr

def dirOf (c : UInt32) : Dir :=
  if isRtl c then .r else if isStrongLtr c then .l else if isDigit c then .en else .n

/-- The paragraph's direction: its first strong character's (left to right
when it has none). -/
def rtlPara (cs : List UInt32) : Bool :=
  match cs.find? (fun c => isRtl c || isStrongLtr c) with
  | some c => isRtl c
  | none => false

/-- Each character's resolved direction (true: right-to-left), none for a
neutral: a digit takes the strong direction before it (`prev`, the
paragraph's at its start). -/
def resolve (prev : Bool) : List UInt32 → List (Option Bool)
  | [] => []
  | c :: t => match dirOf c with
    | .r => some true :: resolve true t
    | .l => some false :: resolve false t
    | .en => some prev :: resolve prev t
    | .n => none :: resolve prev t

/-- For each position, the last resolved direction before it (`p` at the
start). -/
def before (p : Bool) : List (Option Bool) → List Bool
  | [] => []
  | d :: t => p :: before (d.getD p) t

/-- For each position, the first resolved direction at or after it (`p`
past the end). -/
def after (p : Bool) : List (Option Bool) → List Bool
  | [] => []
  | d :: t => let rest := after p t; d.getD (rest.headD p) :: rest

/-- A mark takes the level of the character before it. -/
def markLevels (prev : Nat) : List (UInt32 × Nat) → List Nat
  | [] => []
  | (c, v) :: t => let v' := if isMark c then prev else v; v' :: markLevels v' t

/-- Each character's level (Unicode's bidi algorithm, for one paragraph
with no explicit embeddings): right-to-left at 1; left-to-right at the
paragraph's level rounded up to even; a digit as the strong text before it
makes it (after right-to-left: at 2, kept in order inside the run); a
neutral as the strong directions on both its sides when they agree (a
digit counting as right-to-left after right-to-left), else the
paragraph's. A mark takes its base's level. -/
def levels (cs : List UInt32) : List Nat :=
  let rtl := rtlPara cs
  let p := if rtl then 1 else 0
  let lvl : Bool → Nat := fun r => if r then 1 else (if rtl then 2 else 0)
  let res := resolve rtl cs
  let one : (UInt32 × Option Bool) × Bool × Bool → Nat := fun ((c, d), b, a) =>
    match d with
    | some r => if dirOf c == .en && r then 2 else lvl r
    | none => if b == a then lvl b else p
  let base := ((cs.zip res).zip ((before rtl res).zip (after rtl res))).map one
  markLevels p (cs.zip base)

/-- Reverse every maximal run of entries whose level is at least `lv`
(`run` holds the current run, reversed as it is collected). -/
def reverseRuns (lv : Nat) (run : List (UInt32 × Nat)) : List (UInt32 × Nat) → List (UInt32 × Nat)
  | [] => run
  | x :: t => if x.2 ≥ lv then reverseRuns lv (x :: run) t else run ++ x :: reverseRuns lv [] t

def reverseFrom (lv : Nat) (xs : List (UInt32 × Nat)) : List (UInt32 × Nat) := reverseRuns lv [] xs

/-- Unicode's rule L2: from the highest level down to 1, reverse each
run at that level or above. -/
def reorder (xs : List (UInt32 × Nat)) : List (UInt32 × Nat) :=
  let top := xs.foldl (fun m x => max m x.2) 0
  (List.range top).foldl (fun acc k => reverseFrom (top - k) acc) xs

/-- The line in display order, and whether it is a right-to-left line. -/
def withLevels (cs : List UInt32) : List (UInt32 × Nat) :=
  let lv := levels cs
  cs.mapIdx fun i c => (c, lv.getD i 0)

def visualL (cs : List UInt32) : List UInt32 × Bool :=
  ((reorder (withLevels cs)).map (·.1), rtlPara cs)

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

end Text
