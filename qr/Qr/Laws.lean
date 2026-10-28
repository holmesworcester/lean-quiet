/-
The laws, on the functions the decoder runs (not on a model of them).

Data stream (SegLaws.lean):
- `parse_dataStream`: the data codewords the encoder makes for valid
  segments parse back to those segments.
- `parse_segsBits`: the same at the bit level, for any terminated tail.
- `parse_valid`: whatever `parse` returns is valid (counts fit, digits
  are digits, characters are alphanumeric, ECI numbers below 10⁶), so it
  can be encoded again.

Format and version information (Format.lean):
- `decodeFormat_correct`: a format reading within 3 bits of what was
  written decodes to the level and mask written.
- `decodeVersion_correct`: the same for versions 7 to 40.

Reed–Solomon (here):
- `correct_sound`: a block `RS.correct` returns has zero syndromes —
  c(αʲ) = 0 for every j below the number of error-correction codewords,
  so it is a codeword — has the received block's length, and differs from
  it in at most ⌊k/2⌋ places.
- `correct_clean`: a block that is already a codeword comes back
  unchanged.

Frames:
- `decodeImage_malformed`: a frame whose buffer does not hold its rows
  (or with no pixels, or more than 16384 a side) decodes to `none`.

Totality is Lean's: every function the decoder calls is defined without
`partial`, `unsafe`, fuel, `!`-indexing or `panic`, Lean accepts their
termination (the well-founded ones are `parse` and the segment readers),
and every loop is a `for` over a finite range. tests/check.sh scans for
the escape hatches and checks the laws' axioms.
-/
import Qr.SegLaws
import Qr.Format
import Qr.RS
import Qr.Decode

namespace Qr

namespace RS

theorem dist_self (a : Array UInt8) : dist a a = 0 := by
  simp [dist]

/-- Zero syndromes means the block's polynomial vanishes at α⁰ … α^(k−1),
the roots of the generator: it is a codeword. -/
theorem syndromes_zero {k : Nat} {c : Array UInt8} :
    allZero (syndromes k c) = true ↔ ∀ j < k, eval c (exp j) = 0 := by
  unfold allZero syndromes
  rw [Array.all_eq_true]
  simp

/-- **Soundness of correction.** -/
theorem correct_sound {k : Nat} {r c : Array UInt8} (h : correct k r = some c) :
    (∀ j < k, eval c (exp j) = 0) ∧ c.size = r.size ∧ dist r c ≤ k / 2 := by
  unfold correct at h
  split at h
  · rename_i hz
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨syndromes_zero.mp hz, rfl, by simp [dist_self]⟩
  · split at h
    · simp at h
    · split at h
      · rename_i c' _ hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        exact ⟨syndromes_zero.mp hc.1.1, hc.1.2, hc.2⟩
      · simp at h

/-- **A codeword is left alone.** -/
theorem correct_clean {k : Nat} {r : Array UInt8} (h : ∀ j < k, eval r (exp j) = 0) :
    correct k r = some r := by
  simp [correct, syndromes_zero.mpr h]

end RS

theorem decodeImage_malformed {img : Image} (h : img.wellFormed = false) : decodeImage img = none := by
  simp [decodeImage, h]

end Qr
