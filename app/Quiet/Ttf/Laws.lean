/-
Laws of the running byte reader, cmap lookup and checked rasterizer.
Byte reads expose their bounds proof; cmap results have a matching table
entry and its specified glyph; coverage cannot wrap and the returned
bitmap has exactly its area in bytes, inside its declared overhang.
-/
import Quiet.Ttf.Raster

namespace Ttf

theorem byte_in_bounds (b : ByteArray) (i n : Nat) (h : u8 b i = some n) :
    ∃ hi : i < b.size, b[i].toNat = n := by
  unfold u8 at h
  split at h
  · exact ⟨by assumption, Option.some.inj h⟩
  · cases h

theorem cmap_entry (es : Cmap) (c g : Nat) (h : lookup es c = some g) :
    ∃ e ∈ es, e.contains c = true ∧ e.glyph c = g := by
  unfold lookup at h
  cases hf : es.find? (·.contains c) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨e, List.mem_of_find?_eq_some hf, List.find?_some (p := fun e : Entry => e.contains c) (a := e) hf, h⟩

theorem cmap12_glyph (lo hi first c : Nat) :
    (Entry.mk lo hi (.sequential first)).glyph c = first + c - lo := rfl

theorem cmap4_delta (lo hi c : Nat) (delta : Int) :
    (Entry.mk lo hi (.delta delta)).glyph c = (((c : Int) + delta).emod 65536).toNat := rfl

theorem cmap4_array (lo hi c : Nat) (ids : Array Nat) (delta : Int) :
    (Entry.mk lo hi (.glyphs ids delta)).glyph c =
      let g := ids[c - lo]?.getD 0
      if g == 0 then 0 else ((g : Int) + delta).emod 65536 |>.toNat := rfl

/-- Unlike a byte cast alone, saturation cannot turn opaque into clear. -/
theorem coverage_value (n : Nat) : (coverage n).toNat = min 255 (n * 255 / 64) := by
  simp only [coverage, Nat.toUInt8]
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_left 255 (n * 255 / 64)
  omega

theorem coverage_bound (n : Nat) : (coverage n).toNat ≤ 255 := by
  rw [coverage_value]
  exact Nat.min_le_left _ _

theorem checked_valid (b out : Bitmap) (h : checked b = some out) : out.Valid := by
  unfold checked at h
  split at h
  · cases h; assumption
  · cases h

theorem raster_valid (f : Face) (glyph size cell : Nat) (b : Bitmap)
    (h : raster f glyph size cell = some b) : b.Valid := by
  unfold raster at h
  cases hr : rasterRaw f glyph size cell with
  | none => simp [hr] at h
  | some raw =>
    simp only [hr] at h
    exact checked_valid raw b h

/-- Every coordinate inside a returned bitmap has an in-bounds byte,
whose value is between 0 and 255. -/
theorem raster_pixel (f : Face) (glyph size cell : Nat) (b : Bitmap)
    (h : raster f glyph size cell = some b) (x y : Nat) (hx : x < b.w) (hy : y < b.h) :
    ∃ hi : y * b.w + x < b.pixels.size, b.pixels[y * b.w + x].toNat ≤ 255 := by
  have sized := (raster_valid f glyph size cell b h).1
  have hm := Nat.mul_le_mul_right b.w (Nat.succ_le_of_lt hy)
  have hi : y * b.w + x < b.pixels.size := by
    rw [Nat.succ_mul, Nat.mul_comm b.h b.w] at hm
    omega
  refine ⟨hi, ?_⟩
  have := b.pixels[y * b.w + x].toNat_lt
  omega

/-- The non-vacuity checks exercise the same constructors as raster. -/
theorem ink_witness :
    checked ⟨-1, -1, 2, 2, 1, 1, 1, 0, 1, 0, ⟨#[0, 127, 255, 0]⟩⟩ ≠ none ∧
    coverage 64 = 255 ∧ lookup [⟨65, 90, .sequential 3⟩] 66 = some 4 := by decide

end Ttf
