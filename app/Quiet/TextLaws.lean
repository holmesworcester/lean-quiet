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
- `digits_keep_order`: numbers inside right-to-left text keep their
  order (the cases that showed "25" as "52" and "2024" as "4202").
-/
import Quiet.Text

namespace Text

theorem reverseRuns_perm (lv : Nat) : ∀ (run xs : List (UInt32 × Nat)),
    (reverseRuns lv run xs).Perm (run ++ xs)
  | run, [] => by simp [reverseRuns]
  | run, x :: t => by
    unfold reverseRuns
    split
    · exact (reverseRuns_perm lv (x :: run) t).trans (by simp [List.perm_middle.symm])
    · exact List.Perm.append_left run (List.Perm.cons x ((reverseRuns_perm lv [] t).trans (by simp)))

theorem reverseFrom_perm (lv : Nat) (xs : List (UInt32 × Nat)) : (reverseFrom lv xs).Perm xs := by
  simpa [reverseFrom] using reverseRuns_perm lv [] xs

theorem foldl_reverseFrom_perm (top : Nat) : ∀ (ks : List Nat) (acc : List (UInt32 × Nat)),
    (ks.foldl (fun acc k => reverseFrom (top - k) acc) acc).Perm acc
  | [], _ => List.Perm.refl _
  | k :: t, acc => (foldl_reverseFrom_perm top t _).trans (reverseFrom_perm _ acc)

theorem reorder_perm (xs : List (UInt32 × Nat)) : (reorder xs).Perm xs := by
  unfold reorder
  exact foldl_reverseFrom_perm _ _ xs

theorem withLevels_fst (cs : List UInt32) : (withLevels cs).map (·.1) = cs := by
  apply List.ext_getElem
  · simp [withLevels]
  · intro i h1 h2
    simp [withLevels, List.getElem_mapIdx]

/-- **Bidi drops nothing and adds nothing.** -/
theorem visual_perm (cs : Array UInt32) : (visual cs).1.toList.Perm cs.toList := by
  simp only [visual, visualL]
  have := (reorder_perm (withLevels cs.toList)).map (·.1)
  simpa [withLevels_fst] using this

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

/-- The digits of a line, in display order. -/
def digitsShown (cs : List UInt32) : List UInt32 := (visualL cs).1.filter isDigit

/-- **Numbers in right-to-left text keep their order**: "אני בן 25 שנה"
shows 2 before 5; "Room שלום 2024 עולם" shows 2024. -/
theorem digits_keep_order :
    -- אני בן 25 שנה
    digitsShown [0x5D0, 0x5E0, 0x5D9, 0x20, 0x5D1, 0x5DF, 0x20, 0x32, 0x35, 0x20, 0x5E9, 0x5E0, 0x5D4] = [0x32, 0x35] ∧
    -- Room שלום 2024 עולם
    digitsShown [0x52, 0x6F, 0x6F, 0x6D, 0x20, 0x5E9, 0x5DC, 0x5D5, 0x5DD, 0x20, 0x32, 0x30, 0x32, 0x34, 0x20,
      0x5E2, 0x5D5, 0x5DC, 0x5DD] = [0x32, 0x30, 0x32, 0x34] := by
  decide

end Text
