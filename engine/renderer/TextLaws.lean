/-
What Text draws is what the text says, over the running code (`visual`,
`place`, `oneLine`):

- `visual_perm`: a line in display order is a permutation of the line:
  bidi drops nothing, adds nothing, takes nothing from elsewhere.
- `place_shows`: the glyphs placed are exactly the line's visible
  characters (only invisibles are left out), in display order.
- `oneLine_prefix`: a single line shows the text, or, cut, a logical
  prefix of it and the ellipsis: a long name keeps its beginning in
  either direction.
- `numbers_keep_order`, `arabic_numbers_keep_order`: every maximal
  resolved number run stays contiguous, in logical order, in either direction.
-/
import engine.renderer.Text
import engine.renderer.bidi.Laws

namespace Text

/-- **Bidi drops nothing and adds nothing.** -/
theorem visual_perm (cs : Array UInt32) : (visual cs).1.toList.Perm cs.toList := by
  simpa [visual, visualL, visualIn, List.map_map, Function.comp_def] using
    Bidi.display_perm (rtlPara cs.toList) (cs.toList.map fun c => (c, dirOf c))

theorem placeL_shows (f : Font.Font) : ∀ (cs : List UInt32) (x lastX : Nat),
    (placeL f cs x lastX).1.map (·.c) = cs.filter (fun c => !isInvisible c)
  | [], _, _ => by simp [placeL]
  | c :: t, x, lastX => by
    unfold placeL
    by_cases hi : isInvisible c
    · simp [hi, placeL_shows f t x lastX]
    · by_cases hm : isMark c
      · simp [hi, hm, placeL_shows f t x lastX]
      · simp [hi, hm, placeL_shows f t (x + adv f c) x]

/-- **The glyphs placed are the line's visible characters.** -/
theorem place_shows (f : Font.Font) (cs : Array UInt32) :
    (place f cs).1.toList.map (·.c) = cs.toList.filter (fun c => !isInvisible c) := by
  simp [place, placeL_shows]

/-- What a line shows, as code points in display order. -/
def shown (l : Line) : List UInt32 := l.toList.map (·.c)

theorem shown_shift (l : Line) (d : Nat) : shown (l.map fun g => { g with x := g.x + d }) = shown l := by
  simp [shown, Function.comp_def]

/-- **A single line shows its text, or a logical prefix and the
ellipsis.** Its glyphs are a permutation of the visible characters of the
whole text, or of a prefix of it (in logical order: what is read first)
followed by "…". -/
theorem oneLinePlaced_prefix (f : Font.Font) (width : Nat) (cs : Array UInt32) :
    (shown (oneLinePlaced f width cs).1).Perm (cs.toList.filter (fun c => !isInvisible c)) ∨
    ∃ k, (shown (oneLinePlaced f width cs).1).Perm
      (((cs.toList.take k) ++ [0x2026]).filter (fun c => !isInvisible c)) := by
  unfold oneLinePlaced
  have h := place_shows f (visual cs).1
  rcases hp : place f (visual cs).1 with ⟨placed, w⟩
  rw [hp] at h
  by_cases hw : w ≤ width
  · left
    simp only [hw, if_true, shown]
    rw [h]
    exact (visual_perm cs).filter _
  · right
    refine ⟨fitting f (width - min width (adv f 0x2026)) cs.toList, ?_⟩
    simp only [hw, if_false, shown, place_shows]
    have := (visual_perm (cutTo f width cs)).filter (fun c => !isInvisible c)
    simpa [cutTo, Array.toList_extract, List.extract] using this

theorem oneLine_prefix (f : Font.Font) (width : Nat) (s : String) :
    let cs := shape (f.emoji.emojify (s.toList.toArray.map (·.val)))
    (shown (oneLine f width s)).Perm (cs.toList.filter (fun c => !isInvisible c)) ∨
    ∃ k, (shown (oneLine f width s)).Perm
      (((cs.toList.take k) ++ [0x2026]).filter (fun c => !isInvisible c)) := by
  intro cs
  simp only [oneLine, shown_shift]
  exact oneLinePlaced_prefix f width cs

/-- Maximal EN/AN runs after W1–W5. The renderer uses these same runs;
W2 may turn European digits into AN after an Arabic letter. -/
def numberRuns (kind : Bidi.Class) (rtl : Bool) (cs : List UInt32) : List (List UInt32) :=
  Bidi.numberRuns kind rtl (cs.map fun c => (c, dirOf c))

/-- **Every European-number run is contiguous and keeps logical order,**
for any line and either paragraph direction, including W4 separators and
W5 terminators. EN means the type after W2, before W7. -/
theorem numbers_keep_order (rtl : Bool) (cs run : List UInt32)
    (h : run ∈ numberRuns .en rtl cs) : run <:+: visualIn rtl cs :=
  Bidi.run_contiguous .en rtl _ run h

/-- **Every Arabic-number run is contiguous and keeps logical order,**
including its W4 common separators, in either paragraph direction. -/
theorem arabic_numbers_keep_order (rtl : Bool) (cs run : List UInt32)
    (h : run ∈ numberRuns .an rtl cs) : run <:+: visualIn rtl cs :=
  Bidi.run_contiguous .an rtl _ run h

/-- Non-vacuity, with both W4 and W5: Hebrew, "$12:30%", Hebrew. -/
theorem numbers_witness : ∀ rtl : Bool,
    [0x24, 0x31, 0x32, 0x3A, 0x33, 0x30, 0x25] ∈ numberRuns .en rtl
      [0x5D0, 0x24, 0x31, 0x32, 0x3A, 0x33, 0x30, 0x25, 0x5D1] := by decide

/-- Non-vacuity: Arabic-Indic digits separated by a common separator. -/
theorem arabic_numbers_witness : ∀ rtl : Bool,
    [0x661, 0x2C, 0x662] ∈ numberRuns .an rtl [0x627, 0x661, 0x2C, 0x662, 0x628] := by decide

end Text

namespace Text

/-- Where glyphs of these advances start, from x. -/
def starts (x : Nat) : List Nat → List Nat
  | [] => []
  | a :: t => x :: starts (x + a) t

/-- **No two glyphs overlap.** The glyphs that advance (all but marks)
start exactly where the one before ends: glyph i spans [sᵢ, sᵢ + aᵢ) and
sᵢ₊₁ = sᵢ + aᵢ, from the line's start, in display order. (A mark sits on
its base, with no advance.) -/
theorem place_starts (f : Font.Font) : ∀ (cs : List UInt32) (x lastX : Nat),
    ((placeL f cs x lastX).1.filter (fun g => !isMark g.c)).map (·.x) =
      starts x ((cs.filter fun c => !isInvisible c && !isMark c).map (adv f))
  | [], _, _ => by simp [placeL, starts]
  | c :: t, x, lastX => by
    unfold placeL
    by_cases hi : isInvisible c
    · simp [hi, place_starts f t x lastX]
    · by_cases hm : isMark c
      · simp [hi, hm, place_starts f t x lastX]
      · simp [hi, hm, starts, place_starts f t (x + adv f c) x]

end Text

namespace Text

/-- The explicit bidi controls: embeddings and overrides (U+202A–202E),
isolates (U+2066–2069), and the marks LRM, RLM and ALM (U+200E, U+200F, U+061C). -/
def bidiControls : List UInt32 :=
  [0x202A, 0x202B, 0x202C, 0x202D, 0x202E, 0x2066, 0x2067, 0x2068, 0x2069, 0x200E, 0x200F, 0x061C]

/-- **Directional controls have no directional authority.** They are ON,
not embeddings, overrides, isolates or strong marks. This class law does
not assert invariance under inserting ON characters between numbers. -/
theorem controls_neutral : bidiControls.all (fun c => dirOf c == .on) = true := by decide

theorem marks_invisible : isInvisible 0x200E = true ∧ isInvisible 0x200F = true := by decide

end Text
