/-
The pictures' laws, on the functions the composer runs.

Sizes (`fit`, Pic/Fit.lean):
- `fit_small`: a picture within the edge keeps its size.
- `fit_le`: both sides of a fitted size are at most the edge.
- `fit_pos`: neither side is 0.
- `fit_long`: a larger picture's longer side becomes exactly the edge.
- `fit_round`: its other side is the nearest pixel to the scaled side
  (2·q·l is within l of 2·w·e), unless that rounds to 0 and 1 is used.

The tray (`layout`, Pic/Tray.lean), for any pictures:
- `layout_sizes`: each thumbnail is its picture fitted into the box.
- `layout_inside`: every slot is inside the tray, both ways.
- `layout_apart`: any two slots, in order, are at least `gap` apart, so
  no two thumbnails overlap.

QOI (Pic/Qoi.lean):
- `decode_sized`: whatever bytes it is given, a picture the decoder
  returns has sides of 1 to 2048 and exactly their pixels' bytes.
  (`decode (encode p) = p` is tested, not proven.)

The composer (Pic/Composer.lean):
- `add_stored`: a picture `add` accepts is exactly `fit` of its original
  and well formed, and its stored QOI decodes back to exactly its pixels.
- `scale_wellFormed`, `render_wellFormed`: a scaled picture and the tray
  have exactly their pixels' bytes.
- `render_opaque`: every pixel of the tray has alpha 255, whatever the
  pictures' alpha (a fix: transparent pictures left holes in the tray).
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

/-! ## The tray -/

theorem place_sizes (g : Geom) : ∀ (x : Nat) (ss : List (Nat × Nat)),
    (place g x ss).map (fun s => (s.w, s.h)) = ss.map (fun p => fit p.1 p.2 g.box)
  | _, [] => rfl
  | x, (w, h) :: rest => by
    simp only [place, List.map_cons]
    rw [place_sizes g _ rest]

/-- Every slot from `x` on starts at or after `x`, lies within the tray's
height, and the slots are pairwise at least `gap` apart. -/
theorem place_props (g : Geom) (hg : 2 * g.pad + 1 ≤ g.height) : ∀ (x : Nat) (ss : List (Nat × Nat)),
    (∀ s ∈ place g x ss, x ≤ s.x ∧ g.pad ≤ s.y ∧ s.y + s.h + g.pad ≤ g.height) ∧
    (place g x ss).Pairwise (fun a b => a.x + a.w + g.gap ≤ b.x)
  | _, [] => by simp [place]
  | x, (w, h) :: rest => by
    have ih := place_props g hg (x + (fit w h g.box).1 + g.gap) rest
    have hb : 1 ≤ g.box := by simp [Geom.box]; omega
    have hf := fit_le (w := w) (h := h) hb
    simp only [place, List.mem_cons, List.pairwise_cons]
    refine ⟨?_, ?_, ih.2⟩
    · intro s hs
      rcases hs with rfl | hs
      · simp only [Geom.box] at hf ⊢; omega
      · have := ih.1 s hs; omega
    · intro s hs
      have := ih.1 s hs
      omega

theorem layout_sizes (g : Geom) (ss : List (Nat × Nat)) :
    (layout g ss).1.map (fun s => (s.w, s.h)) = ss.map (fun p => fit p.1 p.2 g.box) :=
  place_sizes g g.pad ss

theorem layout_apart (g : Geom) (hg : 2 * g.pad + 1 ≤ g.height) (ss : List (Nat × Nat)) :
    (layout g ss).1.Pairwise (fun a b => a.x + a.w + g.gap ≤ b.x) :=
  (place_props g hg g.pad ss).2

/-- The last slot ends furthest right. -/
theorem le_last (g : Geom) {l : List Slot} (hp : l.Pairwise (fun a b => a.x + a.w + g.gap ≤ b.x))
    {s last : Slot} (hs : s ∈ l) (hl : l.getLast? = some last) : s.x + s.w ≤ last.x + last.w := by
  induction l with
  | nil => simp at hs
  | cons a rest ih =>
    rw [List.pairwise_cons] at hp
    cases rest with
    | nil =>
      simp at hs hl; subst hs; subst hl; exact Nat.le_refl _
    | cons b rest' =>
      have hl' : (b :: rest').getLast? = some last := by
        simpa [List.getLast?_cons_cons] using hl
      rcases List.mem_cons.mp hs with rfl | hs'
      · have hm : last ∈ b :: rest' := List.mem_of_getLast? hl'
        have := hp.1 last hm
        omega
      · exact ih hp.2 hs' hl'

theorem layout_inside (g : Geom) (hg : 2 * g.pad + 1 ≤ g.height) (ss : List (Nat × Nat)) :
    ∀ s ∈ (layout g ss).1, g.pad ≤ s.x ∧ s.x + s.w + g.pad ≤ (layout g ss).2 ∧
      g.pad ≤ s.y ∧ s.y + s.h + g.pad ≤ g.height := by
  intro s hs
  have hp := place_props g hg g.pad ss
  have h1 := hp.1 s hs
  refine ⟨h1.1, ?_, h1.2⟩
  simp only [layout, width] at hs ⊢
  cases hl : (place g g.pad ss).getLast? with
  | none => simp [List.getLast?_eq_none_iff.mp hl] at hs
  | some last =>
    simp only
    have := le_last g hp.2 hs hl
    omega

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

/-! ## The composer -/

theorem render_wellFormed (g : Geom) (pics : List Rgba) : (render g pics).wellFormed = true := by
  simp [render, Rgba.wellFormed, ByteArray.size]

/-- **The tray is opaque**: every pixel's alpha is 255, whatever the
pictures' alpha (a transparent picture is blended over the ground, never
left as a hole in the tray). -/
theorem render_opaque (g : Geom) (pics : List Rgba) (k : Nat) (hk : k < (render g pics).w * (render g pics).h) :
    (render g pics).px[4 * k + 3]? = some 255 := by
  have mk : ∀ (a : Array UInt8) (i : Nat), (ByteArray.mk a)[i]? = a[i]? := fun _ _ => rfl
  simp only [render] at hk ⊢
  rw [mk, Array.getElem?_ofFn]
  have : 4 * k + 3 < 4 * (layout g (pics.map fun p => (p.w, p.h))).2 * g.height := by
    have := Nat.mul_le_mul_left 4 (Nat.succ_le_of_lt hk)
    rw [Nat.mul_assoc]; omega
  simp only [this, dite_true, trayByte]
  simp [show (4 * k + 3) % 4 = 3 by omega]

theorem scale_wellFormed (src : Rgba) (tw th : Nat) : (scale src tw th).wellFormed = true := by
  simp [scale, Rgba.wellFormed, ByteArray.size]

theorem add_stored {c : Composer} {ow oh w h : Nat} {px : ByteArray} {c' : Composer} {msg : String}
    (hadd : add c ow oh w h px = (c', msg)) (grew : c'.size = c.size + 1) :
    fit ow oh attachEdge = (w, h) ∧ px.size = 4 * w * h ∧
      ∃ a, c' = c.push a ∧ decode a.qoi = some { w, h, px } := by
  unfold add at hadd
  simp only at hadd
  split at hadd
  · simp only [Prod.mk.injEq] at hadd; obtain ⟨rfl, -⟩ := hadd; omega
  · split at hadd
    · simp only [Prod.mk.injEq] at hadd; obtain ⟨rfl, -⟩ := hadd; omega
    · rename_i h1 h2
      split at hadd
      · rename_i back hback
        split at hadd
        · rename_i heq
          obtain ⟨hw, hh, hp⟩ := heq
          simp only [Prod.mk.injEq] at hadd
          obtain ⟨rfl, -⟩ := hadd
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h2
          simp [Rgba.wellFormed] at h1
          refine ⟨h2, by omega, _, rfl, ?_⟩
          rw [hback]
          cases back
          simp_all
        · simp only [Prod.mk.injEq] at hadd; obtain ⟨rfl, -⟩ := hadd; omega
      · simp only [Prod.mk.injEq] at hadd; obtain ⟨rfl, -⟩ := hadd; omega

end Pic
