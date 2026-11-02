/-
The pictures' laws, on the functions the app runs.

Sizes (`fit`, Pic/Fit.lean):
- `fit_small`: a picture within the edge keeps its size.
- `fit_le`: both sides of a fitted size are at most the edge.
- `fit_pos`: neither side is 0.
- `fit_long`: a larger picture's longer side becomes exactly the edge.
- `fit_round`: its other side is the nearest pixel to the scaled side
  (2·q·l is within l of 2·w·e), unless that rounds to 0 and 1 is used.

QOI (Pic/Qoi.lean):
- `decode_sized`: whatever bytes it is given, a picture the decoder
  returns has sides of 1 to 2048 and exactly their pixels' bytes.
  (`decode (encode p) = p` is tested, not proven.)

The tray and the composer (Pic/Tray.lean, Composer.lean) run only in qr's
Android harness; their laws went on 2026-11-01 (no proofs over code the
app does not run; git keeps them). The app sizes a photo it sends by
`fit` (App.preparePhoto) and draws its own chips.
-/
import engine.renderer.pic.Composer

namespace Pic

/-! ## fit -/

theorem fit_small {w h e : Nat} (hs : max w h ≤ e) : fit w h e = (w, h) := by
  simp [fit, hs]

/-- The rounded scaled side is at most the edge (the side is at most the
longer side `l`). -/
theorem scaled_le {w l e : Nat} (hw : w ≤ l) (hl : 0 < l) : (2 * (w * e) + l) / (2 * l) ≤ e := by
  have hm : w * e ≤ l * e := Nat.mul_le_mul_right e hw
  have : (2 * (w * e) + l) / (2 * l) < e + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm e (2 * l), Nat.mul_assoc]
    omega
  omega

theorem fit_le {w h e : Nat} (he : 1 ≤ e) : (fit w h e).1 ≤ e ∧ (fit w h e).2 ≤ e := by
  by_cases hs : max w h ≤ e
  · simp only [fit, hs, ite_true]; omega
  · simp only [fit, hs, ite_false]
    have hl : 0 < max w h := by omega
    have a := scaled_le (w := w) (e := e) (Nat.le_max_left w h) hl
    have b := scaled_le (w := h) (e := e) (Nat.le_max_right w h) hl
    omega

theorem fit_pos {w h e : Nat} (hw : 1 ≤ w) (hh : 1 ≤ h) : 1 ≤ (fit w h e).1 ∧ 1 ≤ (fit w h e).2 := by
  by_cases hs : max w h ≤ e
  · simp only [fit, hs, ite_true]; omega
  · simp only [fit, hs, ite_false]; omega

/-- The longer side, scaled, is the edge. -/
theorem scaled_long {l e : Nat} (hl : 0 < l) : (2 * (l * e) + l) / (2 * l) = e := by
  apply Nat.le_antisymm
  · exact scaled_le (Nat.le_refl l) hl
  · rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm e (2 * l), Nat.mul_assoc]
    omega

theorem fit_long {w h e : Nat} (he : 1 ≤ e) (hl : e < max w h) : max (fit w h e).1 (fit w h e).2 = e := by
  have hn : ¬ max w h ≤ e := by omega
  simp only [fit, hn, ite_false]
  have hl0 : 0 < max w h := by omega
  have a := scaled_le (w := w) (e := e) (Nat.le_max_left w h) hl0
  have b := scaled_le (w := h) (e := e) (Nat.le_max_right w h) hl0
  rcases Nat.le_total h w with hwh | hwh
  · have hm : max w h = w := Nat.max_eq_left hwh
    have := scaled_long (l := w) (e := e) (by omega)
    rw [hm] at a b ⊢
    omega
  · have hm : max w h = h := Nat.max_eq_right hwh
    have := scaled_long (l := h) (e := e) (by omega)
    rw [hm] at a b ⊢
    omega

/-- The scaled side is the nearest pixel: `q = (2we + l) / 2l` has
`2ql ≤ 2we + l < 2ql + 2l`, i.e. |q·l − w·e| ≤ l/2. -/
theorem fit_round {w h e : Nat} (hl : e < max w h) :
    let l := max w h
    let q := (fit w h e).1
    (2 * (q * l) ≤ 2 * (w * e) + l ∨ q = 1) ∧ 2 * (w * e) + l < 2 * (q * l) + 2 * l := by
  intro l q
  have hn : ¬ max w h ≤ e := by omega
  have hq : q = max 1 ((2 * (w * e) + l) / (2 * l)) := by simp [q, fit, hn, l]
  have hl0 : 0 < 2 * l := by simp [l]; omega
  have d1 := Nat.div_mul_le_self (2 * (w * e) + l) (2 * l)
  have d2 := Nat.lt_div_mul_add (a := 2 * (w * e) + l) hl0
  generalize hd : (2 * (w * e) + l) / (2 * l) = d at d1 d2 hq
  have e1 : d * (2 * l) = 2 * (d * l) := Nat.mul_left_comm d 2 l
  rw [e1] at d1 d2
  rcases Nat.lt_or_ge d 1 with h0 | h1
  · have : d = 0 := by omega
    subst this
    have hq1 : q = 1 := by simp [hq]
    refine ⟨Or.inr hq1, ?_⟩
    rw [hq1, Nat.one_mul]
    simp at d2
    omega
  · have hqd : q = d := by rw [hq]; omega
    subst hqd
    exact ⟨Or.inl d1, by omega⟩

/-! ## QOI's decoder -/

theorem pixels_size (b : ByteArray) : ∀ (n : Nat) (s : Dec) (acc out : ByteArray),
    pixels b n s acc = some out → out.size = acc.size + 4 * n
  | 0, _, acc, out, h => by simp [pixels] at h; simp [h]
  | n + 1, s, acc, out, h => by
    simp only [pixels] at h
    split at h
    · simp at h
    · have := pixels_size b n _ _ out h
      simp [ByteArray.size_push] at this
      omega

/-- **What QOI's decoder returns is a picture**: sides of 1 to 2048 and
exactly their pixels' bytes, whatever the input. -/
theorem decode_sized {b : ByteArray} {p : Rgba} (h : decode b = some p) :
    1 ≤ p.w ∧ p.w ≤ maxSide ∧ 1 ≤ p.h ∧ p.h ≤ maxSide ∧ p.wellFormed = true := by
  unfold decode at h
  simp only at h
  split at h
  · simp at h
  · rename_i hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨px, hp, rfl⟩ := h
    have := pixels_size b _ _ _ px hp
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_eq_true, not_or] at hc
    have e0 : ∀ n, (ByteArray.emptyWithCapacity n).size = 0 := fun _ => rfl
    rw [e0] at this
    simp only [Rgba.wellFormed, beq_iff_eq]
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    rw [this, Nat.mul_assoc]; omega

end Pic
