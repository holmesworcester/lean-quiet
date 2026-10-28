/-
What a list frame shows at each content position (pixel rows counted up
from the list's bottom): a line of a row's painted bitmap, the
placeholder of a row not painted yet, the placeholder of older messages
not loaded yet, or blank padding. The app's frame is built from `seen`, so
the law is about what runs.

- `covered`: no position inside the rows, nor above them while older
  rows are still to load, is blank. A slow read or decode leaves
  placeholders, never an empty screen.
- `line_painted`: a bitmap line is shown only where the row's bitmap has
  that line.
-/
namespace Cover

inductive Px where
  /-- Row i's bitmap line li (top down). -/
  | line (i li : Nat)
  /-- Row i, not painted yet (or painted at another height). -/
  | hold (i : Nat)
  /-- Above the loaded rows, while older ones are still to load. -/
  | older
  /-- Padding below the first row, or above the last with nothing older. -/
  | blank
  deriving DecidableEq, Repr

/-- The row covering p, from row i whose bottom is y up; each row is its
height and its painted bitmap's height, if painted. -/
def find (p : Nat) : Nat → Nat → List (Nat × Option Nat) → Option Px
  | _, _, [] => none
  | i, y, (h, pt) :: t =>
    if p < y + h then
      let li := y + h - 1 - p
      some (match pt with
        | some bh => if li < bh then .line i li else .hold i
        | none => .hold i)
    else find p (i + 1) (y + h) t

/-- What content position p shows: rows from `bottom` up, older rows
above them if `more`. -/
def seen (bottom : Nat) (more : Bool) (rows : List (Nat × Option Nat)) (p : Nat) : Px :=
  if p < bottom then .blank
  else match find p 0 bottom rows with
    | some x => x
    | none => if more then .older else .blank

theorem find_some (p : Nat) : ∀ (rows : List (Nat × Option Nat)) (i y : Nat),
    y ≤ p → p < y + (rows.map (·.1)).sum → ∃ x, find p i y rows = some x ∧ x ≠ .blank
  | [], _, _, _, h => by simp at h; omega
  | (h, pt) :: t, i, y, hy, hp => by
    unfold find
    by_cases hc : p < y + h
    · simp only [hc, ite_true]
      refine ⟨_, rfl, ?_⟩
      cases pt with
      | none => simp
      | some bh => dsimp; split <;> simp
    · simp only [hc, ite_false]
      simp only [List.map_cons, List.sum_cons] at hp
      exact find_some p t (i + 1) (y + h) (by omega) (by omega)

theorem find_blank (p : Nat) : ∀ (rows : List (Nat × Option Nat)) (i y : Nat),
    find p i y rows ≠ some .blank
  | [], _, _ => by simp [find]
  | (h, pt) :: t, i, y => by
    unfold find
    split
    · cases pt with
      | none => simp
      | some bh => dsimp; split <;> simp
    · exact find_blank p t (i + 1) (y + h)

/-- **Nothing inside the content is blank:** a position at or above the
first row's bottom, below the last row's top or anywhere above it while
older rows are to load, shows a row's line, a placeholder, or older. -/
theorem covered (bottom : Nat) (more : Bool) (rows : List (Nat × Option Nat)) (p : Nat)
    (lo : bottom ≤ p) (hi : p < bottom + (rows.map (·.1)).sum ∨ more = true) :
    seen bottom more rows p ≠ .blank := by
  unfold seen
  simp only [show ¬ p < bottom by omega, ite_false]
  split
  · next x hx => intro h; subst h; exact find_blank p rows 0 bottom hx
  · next hx =>
    rcases hi with hi | hm
    · obtain ⟨x, hx', _⟩ := find_some p rows 0 bottom lo hi
      rw [hx] at hx'; exact absurd hx' (by simp)
    · simp [hm]

theorem find_line (p : Nat) : ∀ (rows : List (Nat × Option Nat)) (i y j li : Nat),
    find p i y rows = some (.line j li) → ∃ h bh, rows[j - i]? = some (h, some bh) ∧ li < bh ∧ i ≤ j
  | [], _, _, _, _, hf => by simp [find] at hf
  | (h, pt) :: t, i, y, j, li, hf => by
    unfold find at hf
    split at hf
    · cases pt with
      | none => simp at hf
      | some bh =>
        dsimp at hf
        split at hf
        · next hl =>
          simp only [Option.some.injEq, Px.line.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          exact ⟨h, bh, by simp, hl, Nat.le_refl _⟩
        · simp at hf
    · obtain ⟨h', bh, hr, hl, hij⟩ := find_line p t (i + 1) (y + h) j li hf
      refine ⟨h', bh, ?_, hl, by omega⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using hr

/-- **A bitmap line is shown only where the row has one:** row j is
painted, and its bitmap has line li. -/
theorem line_painted (bottom : Nat) (more : Bool) (rows : List (Nat × Option Nat)) (p j li : Nat)
    (h : seen bottom more rows p = .line j li) : ∃ hj bh, rows[j]? = some (hj, some bh) ∧ li < bh := by
  unfold seen at h
  split at h
  · simp at h
  · split at h
    · next x hx =>
      subst h
      obtain ⟨hj, bh, hr, hl, _⟩ := find_line p rows 0 bottom j li hx
      exact ⟨hj, bh, by simpa using hr, hl⟩
    · split at h <;> simp at h

end Cover
