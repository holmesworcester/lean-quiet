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
- **Bidi.** In each line, a run of right-to-left characters (Hebrew,
  Arabic) and the neutral characters between them is reversed; a line
  whose first strong character is right-to-left also reverses the order
  of its runs and sits at the right edge.

Not handled: scripts that reorder or stack (Devanagari and other Indic
scripts), ligatures, and emoji sequences (ZWJ, skin tones), which draw
their parts.
-/
import Quiet.Font

namespace Text
open Font

/-- A glyph placed on a line: its code point and x (from the line's start). -/
structure Placed where
  c : UInt32
  x : Nat
  deriving Inhabited

abbrev Line := Array Placed

def inRange (c lo hi : UInt32) : Bool := lo ≤ c && c ≤ hi

/-- Marks: no advance, drawn on the glyph before. -/
def isMark (c : UInt32) : Bool :=
  inRange c 0x0300 0x036F || inRange c 0x0483 0x0489 || inRange c 0x0591 0x05BD ||
  c == 0x05BF || inRange c 0x05C1 0x05C2 || inRange c 0x05C4 0x05C5 || c == 0x05C7 ||
  inRange c 0x0610 0x061A || inRange c 0x064B 0x065F || c == 0x0670 ||
  inRange c 0x06D6 0x06DC || inRange c 0x06DF 0x06E4 || inRange c 0x06E7 0x06E8 ||
  inRange c 0x06EA 0x06ED || c == 0x0E31 || inRange c 0x0E34 0x0E3A || inRange c 0x0E47 0x0E4E ||
  inRange c 0x1AB0 0x1AFF || inRange c 0x1DC0 0x1DFF || inRange c 0x20D0 0x20FF ||
  inRange c 0xFE20 0xFE2F

/-- Drawn as nothing at all. -/
def isInvisible (c : UInt32) : Bool :=
  inRange c 0x200B 0x200F || inRange c 0x2060 0x2064 || inRange c 0xFE00 0xFE0F ||
  c == 0xFEFF || inRange c 0x1F3FB 0x1F3FF

def isRtl (c : UInt32) : Bool :=
  inRange c 0x0590 0x05FF || inRange c 0x0600 0x06FF || inRange c 0xFB1D 0xFDFF ||
  inRange c 0xFE70 0xFEFF

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

/-- Paragraphs (split at newlines) into lines of at most `width` pixels,
as code points in logical order. -/
def wrapPara (f : Font) (width : Nat) (cs : Array UInt32) : Array (Array UInt32) := Id.run do
  let mut lines : Array (Array UInt32) := #[]
  let mut cur : Array UInt32 := #[]
  let mut curW := 0
  -- the start (in cur) of the word being built, and its width so far
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let a := adv f c
    if isSpace c then
      cur := cur.push c; curW := curW + a; i := i + 1
      continue
    -- a word: up to the next space; wide characters are words of their own
    let mut j := i
    let mut w := 0
    if wide f c then
      j := i + 1; w := a
      while j < cs.size && adv f cs[j]! == 0 do j := j + 1
    else
      while j < cs.size && !isSpace cs[j]! && (!wide f cs[j]! || j == i) do
        w := w + adv f cs[j]!; j := j + 1
    if curW + w ≤ width then
      cur := cur ++ cs.extract i j; curW := curW + w
    else if w ≤ width then
      -- the trailing spaces of the line are dropped
      while cur.size > 0 && isSpace cur.back! do cur := cur.pop
      lines := lines.push cur
      cur := cs.extract i j; curW := w
    else
      -- longer than a line: break inside it
      for k in [i:j] do
        let ck := cs[k]!
        let ak := adv f ck
        if curW + ak > width && cur.size > 0 then
          lines := lines.push cur; cur := #[]; curW := 0
        cur := cur.push ck; curW := curW + ak
    i := j
  while cur.size > 0 && isSpace cur.back! do cur := cur.pop
  return lines.push cur

/-! ## Bidi and placing -/

/-- The line in display order: right-to-left runs reversed (with the
neutrals between their characters), and, in a right-to-left line, the
runs' order too. -/
def visual (cs : Array UInt32) : Array UInt32 × Bool := Id.run do
  let rtlLine := match cs.find? (fun c => isRtl c || isStrongLtr c) with
    | some c => isRtl c
    | none => false
  -- runs: maximal stretches that are RTL, or LTR; neutrals join an RTL
  -- run when RTL characters are on both sides
  let n := cs.size
  let mut kinds : Array Bool := Array.replicate n false
  for i in [0:n] do
    kinds := kinds.set! i (isRtl cs[i]!)
  -- a mark takes its base's direction
  for i in [1:n] do
    if isMark cs[i]! then kinds := kinds.set! i kinds[i-1]!
  -- neutrals between two RTL characters are RTL
  let strong (c : UInt32) := isRtl c || isStrongLtr c
  let mut i := 0
  while i < n do
    if !strong cs[i]! && !kinds[i]! then
      let mut j := i
      while j < n && !strong cs[j]! do j := j + 1
      let before := i > 0 && kinds[i-1]!
      let after := j < n && isRtl cs[j]!
      let edge := (i == 0 || j == n) && rtlLine && (before || after)
      if (before && after) || edge then
        for k in [i:j] do kinds := kinds.set! k true
      i := j
    else i := i + 1
  -- split into runs, reverse the RTL ones, and in an RTL line their order
  let mut runs : Array (Array UInt32 × Bool) := #[]
  let mut k := 0
  while k < n do
    let d := kinds[k]!
    let mut j := k
    while j < n && kinds[j]! == d do j := j + 1
    let run := cs.extract k j
    runs := runs.push (if d then run.reverse else run, d)
    k := j
  let ordered := if rtlLine then runs.reverse else runs
  return (ordered.foldl (fun acc r => acc ++ r.1) #[], rtlLine)

/-- A display-order line's glyphs placed from x = 0; a mark sits on the
glyph before it (after it, in a reversed run, where its base now
follows it). -/
def place (f : Font) (cs : Array UInt32) : Line × Nat := Id.run do
  let mut out : Line := #[]
  let mut x := 0
  let mut lastX := 0
  for i in [0:cs.size] do
    let c := cs[i]!
    if isInvisible c then continue
    if isMark c then
      -- in a reversed run the base is the next non-mark glyph
      let base := if i + 1 < cs.size && isRtl c then x else lastX
      out := out.push ⟨c, base⟩
    else
      out := out.push ⟨c, x⟩
      lastX := x
      x := x + adv f c
  return (out, x)

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

/-- A single line, cut to `width` with an ellipsis when longer. -/
def oneLine (f : Font) (width : Nat) (s : String) : Line := Id.run do
  let cs := shape (f.emoji.emojify (s.toList.toArray.map (·.val)))
  let (vis, _) := visual cs
  let (placed, w) := place f vis
  if w ≤ width then return placed
  let ell := adv f 0x2026
  return (placed.filter (·.x + f.cell / 2 + ell ≤ width)).push ⟨0x2026, width - ell⟩

end Text
