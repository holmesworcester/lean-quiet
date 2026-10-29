/- Laws of the translation, crop and selector compiled into every shell.
Cover supplies the frame's content contract; we prove its composition
with a frozen frame at every OS offset, including outside that frame.
The witnesses include painted, pending, and wholly uncovered viewports. -/
import engine.renderer.Translate
import engine.renderer.Input
import engine.renderer.Hold
import Init.Data.SInt.Lemmas
namespace Translate
open Geometry

theorem equivariance (g : Geom) (over bf base sample height r : Nat) :
    row (Surface.make g false over bf base height) sample r =
      Seam.place g over bf sample r := by
  simp [row, position, Surface.make, Seam.place]; omega

theorem pinned (g : Geom) (over bf base height r : Nat) (sample : Int) :
    row (Surface.make g true over bf base height) sample r = Seam.pinned g over r := by
  simp [row, position, Surface.make, Seam.pinned]

theorem source_iff (pin : Bool) (base origin sample y : Int) (height r : Nat) :
    source pin base origin sample height y = some r ↔
      r < height ∧ y = position pin base origin sample + r := by
  unfold source
  dsimp only
  split <;> simp_all <;> omega

theorem copied_row (pin : Bool) (base origin sample : Int) (height top bottom r y : Nat)
    (hs : source pin base origin sample height y = some r)
    (lo : top ≤ y) (hi : y < bottom) :
    let q := rect pin base origin sample height top bottom
    q.src0 ≤ r ∧ r < q.src1 ∧ (q.dst0 : Int) + (r - q.src0 : Nat) = y := by
  obtain ⟨hr, hy⟩ := (source_iff pin base origin sample y height r).mp hs
  have h := Surface.crop_row (position pin base origin sample) height top bottom r hr
    (by omega) (by omega)
  simpa [rect, ← hy] using h

/-- Arbitrary signed OS offsets cannot uncover the fill plane. -/
theorem fill_covers (pin : Bool) (base sample : Int) (top bottom : Nat) (fit : top ≤ bottom) :
    (fillRect pin base sample top bottom).dst0 = top ∧
    (fillRect pin base sample top bottom).dst1 = bottom := by
  unfold fillRect fillOrigin Surface.crop
  have hm := Int.emod_nonneg ((if pin then base else sample) + bottom - top) (by decide : (48 : Int) ≠ 0)
  have hh := Int.emod_lt_of_pos ((if pin then base else sample) + bottom - top) (by decide : (0 : Int) < 48)
  dsimp
  omega

theorem fill_index (pin : Bool) (base sample : Int) (top bottom y : Nat)
    (lo : top ≤ y) (hi : y < bottom) :
    0 ≤ (y : Int) - fillOrigin pin base sample top bottom ∧
    ((y : Int) - fillOrigin pin base sample top bottom).toNat < bottom - top + 48 := by
  unfold fillOrigin
  have hm := Int.emod_nonneg ((if pin then base else sample) + bottom - top) (by decide : (48 : Int) ≠ 0)
  have hh := Int.emod_lt_of_pos ((if pin then base else sample) + bottom - top) (by decide : (0 : Int) < 48)
  omega

/-- Moving tile phase, with the same reversed 48 lines Hold.plane publishes. -/
theorem tile_phase (base sample : Int) (top bottom y : Nat) (lo : top ≤ y) (hi : y < bottom) :
    47 - ((y : Int) - fillOrigin false base sample top bottom).toNat % 48 =
      (content sample bottom y % 48).toNat := by
  have h := fill_index false base sample top bottom y lo hi
  simp only [fillOrigin, content, Bool.false_eq_true, ite_false] at *
  omega

/-- A translated source row still names exactly the content drawn at y. -/
theorem source_content (g : Geom) (fit : g.Fits) (over bf base height r y : Nat) (sample : Int)
    (hs : source false base (Surface.make g false over bf base height).origin sample height y = some r) :
    (bf : Int) + g.view + over - 1 - r = content sample g.composerTop y := by
  have h := (source_iff false base (Surface.make g false over bf base height).origin sample y height r).mp hs
  have hg := Geometry.view_shift g fit
  simp only [Surface.make, position, Bool.false_eq_true, ite_false, Seam.place] at h
  unfold content
  omega

/-- Outside the published extent there is always a placeholder. -/
theorem outside (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int)
    (h : source f.pin f.b f.origin sample height y = none) :
    seen f height high pad bottom more rows sample y = .unloaded := by simp [seen, h]

/-- Composition with main's Cover: the inside branch is Cover.seen at its content
position; Cover.covered excludes blank there. Outside needs no freshness. -/
theorem covered (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int)
    (inside : ∀ r, source f.pin f.b f.origin sample height y = some r →
      pad ≤ (high - 1 - r).toNat ∧
      ((high - 1 - r).toNat < bottom + (rows.map (·.1)).sum ∨ more = true)) :
    seen f height high pad bottom more rows sample y ≠ .blank := by
  unfold seen
  split
  · next r hr => exact Cover.covered pad bottom more rows _ (inside r hr).1 (inside r hr).2
  · simp

theorem line_painted (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int) (j li : Nat)
    (h : seen f height high pad bottom more rows sample y = .line j li) :
    ∃ hj bh, rows[j]? = some (hj, some bh) ∧ li < bh := by
  unfold seen at h
  split at h
  · exact Cover.line_painted pad bottom more rows _ j li h
  · cases h

/-- The exported list rectangle is exactly the proved crop, serialized. -/
theorem edge_list (which : UInt8) (pin : Bool) (base : UInt32) (origin : Int32)
    (height top bottom : UInt32) (sample : Int32) :
    edge false which pin base origin height top bottom sample =
      let q := rect pin base.toNat origin.toInt sample.toInt height.toNat top.toNat bottom.toNat
      (if which == 0 then q.src0 else if which == 1 then q.src1
        else if which == 2 then q.dst0 else q.dst1).toUInt32 := rfl

/-- Both exported fill edges cover exactly the visible interval. -/
theorem edge_fill (pin : Bool) (base : UInt32) (origin : Int32)
    (height top bottom : UInt32) (sample : Int32) (fit : top.toNat ≤ bottom.toNat) :
    edge true 2 pin base origin height top bottom sample = top ∧
    edge true 3 pin base origin height top bottom sample = bottom := by
  have h := fill_covers pin base.toNat sample.toInt top.toNat bottom.toNat fit
  change (fillRect pin base.toNat sample.toInt top.toNat bottom.toNat).dst0.toUInt32 = top ∧
    (fillRect pin base.toNat sample.toInt top.toNat bottom.toNat).dst1.toUInt32 = bottom
  rw [h.1, h.2]
  simp

/-- The scalar selector really returns the proved row, or -1 for fill. -/
theorem pick_source (pin : Bool) (base : UInt32) (origin : Int32) (height : UInt32)
    (sample : Int32) (y : UInt32) :
    (pick pin base origin height sample y).toInt =
      match source pin base.toNat origin.toInt sample.toInt height.toNat y.toNat with
      | some r => (r : Int)
      | none => -1 := by
  unfold pick
  split
  · next r hr =>
    have h := ((source_iff pin base.toNat origin.toInt sample.toInt y.toNat height.toNat r).mp hr).1
    have hh := height.toNat_lt
    simp only [hr, Int.toInt64, Int64.toInt_ofInt]
    change (r : Int).bmod 18446744073709551616 = r
    apply Int.bmod_eq_of_le <;> omega
  · next hn => simp only [hn]; rfl

theorem hold_row (s : Hold.St) (height r : Nat) (hr : r < height + 48) :
    (Hold.plane s height)[r]! = Hold.holdLine s (47 - r % 48) := by
  simp [Hold.plane, Hold.tile, hr, Nat.mod_lt _ (by decide : 0 < 48)]

/-- Exact pixels: the native fill-plane index selects holdLine at p mod 48. -/
theorem fill_pixel (s : Hold.St) (base top bottom : UInt32) (sample : Int32) (y : UInt32)
    (lo : top.toNat ≤ y.toNat) (hi : y.toNat < bottom.toNat)
    (size : bottom.toNat - top.toNat + 48 < UInt32.size) :
    (Hold.plane s (bottom.toNat - top.toNat))[
      (fillRow false base top bottom sample y).toNat]! =
      Hold.holdLine s (content sample.toInt bottom.toNat y.toNat % 48).toNat := by
  have hr := (fill_index false base.toNat sample.toInt top.toNat bottom.toNat y.toNat lo hi).2
  have hw : ((y.toNat : Int) - fillOrigin false base.toNat sample.toInt top.toNat bottom.toNat).toNat < UInt32.size := by omega
  unfold fillRow
  rw [UInt32.toNat_ofNat_of_lt' hw, hold_row s _ _ hr, tile_phase _ _ _ _ _ lo hi]

/-- Signed displacement in the raw touch ABI (no offset clamp). -/
theorem delta_value (pin : Bool) (base : UInt32) (sample : Int32)
    (lo : -2147483648 ≤ (if pin then 0 else sample.toInt - base.toNat : Int))
    (hi : (if pin then 0 else sample.toInt - base.toNat : Int) < 2147483648) :
    (delta pin base sample).toInt = if pin then 0 else sample.toInt - base.toNat := by
  unfold delta
  simp only [Int.toInt32, Int32.toInt_ofInt]
  change (if pin then 0 else sample.toInt - base.toNat : Int).bmod 4294967296 = _
  apply Int.bmod_eq_of_le <;> omega

/-- The tap mapper uses the translated image's content position. -/
theorem tap_content (f : Surface.Frame) (pin : f.pin = false) (sample y : Int) :
    Input.content { f with slide := sample - f.b } y = content sample f.g.composerTop y := by
  simp [Input.content, pin, content]; omega

theorem witnesses :
    let g : Geom := ⟨200, 0, 0, 20, 20⟩
    let f := Surface.make g false 8 100 100 176
    seen f 176 268 0 0 false [(500, some 500)] 100 20 = .line 0 240 ∧
    seen f 176 268 0 0 false [(500, none)] 100 20 = .hold 0 ∧
    seen f 176 268 0 0 false [] 500 20 = .unloaded ∧
    (fillRect false 100 (-500) 20 180).dst0 = 20 ∧
    (fillRect false 100 (-500) 20 180).dst1 = 180 := by decide
end Translate
