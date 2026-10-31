import engine.renderer.pic.Laws

/-! Synthetic camera/thumbnail fixtures, not a captured user's photo.
Each named check applies the actual README theorem after constructing its
premises. Separate kernel computations pin down the intended output.
No native_decide, axioms, sorry, or assumed fixture premises. -/
namespace Vacuity.Pictures

-- An already-small landscape photo stays unchanged.
theorem small : Pic.fit 640 480 2048 = (640, 480) :=
  Pic.fit_small (by decide)

-- A 12 MP landscape photo is reduced to the attachment limit.
theorem bounded : (Pic.fit 4032 3024 2048).1 ≤ 2048 ∧
    (Pic.fit 4032 3024 2048).2 ≤ 2048 := Pic.fit_le (by decide)

theorem positive : 1 ≤ (Pic.fit 4032 3024 2048).1 ∧
    1 ≤ (Pic.fit 4032 3024 2048).2 := Pic.fit_pos (by decide) (by decide)

theorem longSide : max (Pic.fit 4032 3024 2048).1
    (Pic.fit 4032 3024 2048).2 = 2048 := Pic.fit_long (by decide) (by decide)

-- Portrait photo: exercises rounding on the shorter (first) side.
theorem rounding :
    let l := max 3024 4032
    let q := (Pic.fit 3024 4032 2048).1
    (2 * (q * l) ≤ 2 * 3024 * 2048 + l ∨ q = 1) ∧
    2 * 3024 * 2048 + l < 2 * (q * l) + 2 * l :=
  Pic.fit_round (by decide)

example : Pic.fit 4032 3024 2048 = (2048, 1536) := by decide
example : Pic.fit 3024 4032 2048 = (1536, 2048) := by decide
example : Pic.fit 4032 3024 72 = (72, 54) := by decide
-- Extreme aspect ratio exercises the minimum-one-pixel branch.
example : Pic.fit 1 4032 72 = (1, 72) := by decide
example : Pic.fit 4032 1 72 = (72, 1) := by decide
-- A real rounding case (non-integral scaled shorter side).
example : Pic.fit 1001 2000 72 = (36, 72) := by decide

-- Negative controls: each guards a premise or a meaningful stronger claim.
example : ¬ max 4032 3024 ≤ 2048 := by decide
example : ¬ 1 ≤ (0 : Nat) := by decide
example : ¬ 1 ≤ (0 : Nat) ∧ Pic.fit 0 480 2048 = (0, 480) := by decide
example : ¬ 2048 < max 640 480 := by decide
example : Pic.fit 4032 3024 2048 ≠ (4032, 3024) := by decide
-- Positive dimensions alone do not imply a zero edge bounds the result.
example : ¬ ((Pic.fit 4032 3024 0).1 ≤ 0) := by decide

end Vacuity.Pictures

#print axioms Vacuity.Pictures.small
#print axioms Vacuity.Pictures.bounded
#print axioms Vacuity.Pictures.positive
#print axioms Vacuity.Pictures.longSide
#print axioms Vacuity.Pictures.rounding
