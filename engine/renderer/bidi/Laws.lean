/-
Laws of the running paragraph bidi: permutation, and every maximal EN or
AN run is a contiguous block in logical order in either paragraph
direction. The run definition is Basic.runs, after W1–W5; no distinctness
assumption on characters is needed. The generic laws also apply to
logical indices, so repeated digits cannot conceal a reordering.
-/
import engine.renderer.bidi.Basic

namespace Text.Bidi

theorem w1_keeps (p : Class) (xs : List (α × Class)) :
    (w1 p xs).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [w1, ih]

theorem w23_keeps (p : Class) (xs : List (α × Class)) :
    (w23 p xs).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [w23, ih]

theorem w4_keeps (p : Class) (xs : List (α × Class)) :
    (w4 p xs).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [w4, ih]

theorem et_keeps (p : Bool) (xs : List (α × Class)) :
    (et p xs).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [et, ih]

theorem weak_keeps (p : Bool) (xs : List (α × Class)) :
    (weak p xs).map Prod.fst = xs.map Prod.fst := by
  simp [weak, List.map_reverse, et_keeps, w4_keeps, w23_keeps, w1_keeps]

theorem runs_keeps (xs : List (α × Class)) :
    (runs xs).flatMap Block.chars = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨x, d⟩
    simp only [runs]
    split <;> rename_i h
    · simpa [h] using congrArg (x :: ·) ih
    · split <;> simpa [List.flatMap, h] using congrArg (x :: ·) ih

theorem attach_keeps (p : Nat) (bs : List (Block α)) (vs : List Nat) :
    (attach p bs vs).map Prod.fst = bs := by
  induction bs generalizing vs with
  | nil => rfl
  | cons b bs ih => simp [attach, ih]

theorem reset_keeps (p : Nat) (xs : List (Block α × Nat)) :
    (reset p xs).1.map Prod.fst = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reset, ih]

theorem leveled_keeps (p : Bool) (bs : List (Block α)) :
    (leveled p bs).map Prod.fst = bs := by
  simp [leveled, reset_keeps, attach_keeps]

theorem reverseRuns_perm (lv : Nat) : ∀ (run xs : List (α × Nat)),
    (reverseRuns lv run xs).Perm (run ++ xs)
  | run, [] => by simp [reverseRuns]
  | run, x :: t => by
    unfold reverseRuns
    split
    · exact (reverseRuns_perm lv (x :: run) t).trans (by simp [List.perm_middle.symm])
    · exact List.Perm.append_left run (List.Perm.cons x ((reverseRuns_perm lv [] t).trans (by simp)))

theorem reorder_perm (xs : List (α × Nat)) : (reorder xs).Perm xs := by
  exact (reverseRuns_perm 1 [] _).trans (by simpa using reverseRuns_perm 2 [] xs)

theorem display_perm (p : Bool) (xs : List (α × Class)) :
    (display p xs).Perm (xs.map Prod.fst) := by
  have h := ((reorder_perm (leveled p (blocks p xs))).map Prod.fst).flatMap_right Block.chars
  simpa [display, leveled_keeps, blocks, runs_keeps, weak_keeps, List.flatMap_map, ← List.map_flatMap, List.map_map, Function.comp_def] using h

/-- Every block selected by the shared run definition survives as an
infix, in logical order. Applies to indices as well as code points. -/
theorem run_contiguous (kind : Class) (p : Bool) (xs : List (α × Class)) (run : List α)
    (h : run ∈ numberRuns kind p xs) : run <:+: display p xs := by
  simp only [numberRuns, List.mem_map, List.mem_filter] at h
  obtain ⟨b, ⟨hb, _⟩, rfl⟩ := h
  have hp := (reorder_perm (leveled p (blocks p xs))).map Prod.fst
  rw [leveled_keeps] at hp
  have hm := hp.mem_iff.mpr hb
  have hf : b.chars ∈ ((reorder (leveled p (blocks p xs))).map (fun b => b.1.chars)) := by
    simpa only [List.map_map, Function.comp_def] using List.mem_map_of_mem (f := Block.chars) hm
  exact List.infix_of_mem_flatten hf

end Text.Bidi
