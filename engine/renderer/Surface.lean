/-
Placement computed in Lean and copied by every shell. The frame publishes
cropped rectangles. The row laws connect their origin to Geometry, for
both conversations and pinned pages; offset_bounds covers OS samples.
-/
import engine.renderer.Geometry
namespace Surface
open Geometry

def offset (maxB : Nat) (sample : Int) : Nat := min sample.toNat maxB

structure Rect where
  src0 : Nat
  src1 : Nat
  dst0 : Nat
  dst1 : Nat
  deriving Inhabited, BEq, Repr

structure Frame where
  g : Geom
  pin : Bool
  b : Nat
  origin : Int
  list : Rect
  header : Rect
  composer : Rect
  slide : Int := 0
  deriving Inhabited, BEq, Repr

def crop (origin : Int) (height lo hi : Nat) : Rect :=
  let a := min height ((lo : Int) - origin).toNat
  let z := max a (min height ((hi : Int) - origin).toNat)
  ⟨a, z, (origin + a).toNat, (origin + z).toNat⟩

def make (g : Geom) (pin : Bool) (over bf bn height : Nat) : Frame :=
  let origin := if pin then Seam.pinned g over 0 else Seam.place g over bf bn 0
  ⟨g, pin, bn, origin, crop origin height g.top g.composerTop,
    ⟨0, g.top, 0, g.top⟩, ⟨0, g.h - g.composerTop, g.composerTop, g.h⟩, 0⟩

def Frame.row (f : Frame) (r : Nat) : Int := f.origin + r

def Rect.words (r : Rect) : Array UInt32 :=
  #[r.src0.toUInt32, r.src1.toUInt32, r.dst0.toUInt32, r.dst1.toUInt32]

/-- Three source/destination rectangles, fill interval, viewport and offset. -/
def Frame.words (f : Frame) : Array UInt32 :=
  f.list.words ++ f.header.words ++ f.composer.words ++
    #[(f.g.composerTop + f.g.bot).toUInt32, f.g.h.toUInt32,
      f.g.viewNow.toUInt32, f.b.toUInt32]

/-- The navigation/keyboard area repeats the composer's last pixel row.
This padding is published as pixels, not reconstructed by a shell. -/
def fill (g : Geom) (bot : Array ByteArray) : Array ByteArray :=
  bot ++ Array.replicate (g.h - g.composerTop - bot.size) (bot.back?.getD .empty)

/-- Raster copying of the same rectangles used by the shells. -/
def compose (words : Array UInt32) (height : Nat) (bg : ByteArray)
    (list top bot : Array ByteArray) : Array ByteArray := Id.run do
  let mut out := Array.replicate height bg
  for (layer, k) in [(list, 0), (top, 4), (bot, 8)] do
    let src := words[k]!.toNat
    let dst := words[k + 2]!.toNat
    for r in [0:words[k + 1]!.toNat - src] do
      if let some row := layer[src + r]? then out := out.set! (dst + r) row
  if let some row := bot.back? then
    for r in [words[12]!.toNat:min height words[13]!.toNat] do out := out.set! r row
  return out

/-- A buffer row inside the clip is copied to exactly origin + row. -/
theorem crop_row (origin : Int) (height lo hi r : Nat)
    (hr : r < height) (hl : (lo : Int) ≤ origin + r) (hh : origin + r < hi) :
    (crop origin height lo hi).src0 ≤ r ∧ r < (crop origin height lo hi).src1 ∧
    ((crop origin height lo hi).dst0 : Int) + (r - (crop origin height lo hi).src0 : Nat) =
      origin + r := by
  unfold crop
  dsimp
  omega

/-- The composer rectangle carries Geometry's composerTop unchanged. -/
theorem composer_top (g : Geom) (pin : Bool) (over bf bn height : Nat) :
    (make g pin over bf bn height).composer.dst0 = g.composerTop := rfl

/-- Even the serialized rectangle used by C copies the row to row's home.
The size premises are the physical buffer/coordinate limits of the ABI. -/
theorem published_row (g : Geom) (pin : Bool) (over bf bn height r : Nat)
    (hr : r < height)
    (hl : (g.top : Int) ≤ (make g pin over bf bn height).row r)
    (hh : (make g pin over bf bn height).row r < g.composerTop)
    (hs : (make g pin over bf bn height).list.src0 < UInt32.size)
    (hd : (make g pin over bf bn height).list.dst0 < UInt32.size) :
    let f := make g pin over bf bn height
    (f.words[2]!.toNat : Int) + (r - f.words[0]!.toNat : Nat) = f.row r := by
  let f := make g pin over bf bn height
  have h := crop_row f.origin height g.top g.composerTop r hr hl hh
  have h0 : f.words[0]! = f.list.src0.toUInt32 := by simp [Frame.words, Rect.words]
  have h2 : f.words[2]! = f.list.dst0.toUInt32 := by simp [Frame.words, Rect.words]
  change (f.words[2]!.toNat : Int) + (r - f.words[0]!.toNat : Nat) = f.row r
  rw [h0, h2]
  rw [show f.list.dst0.toUInt32.toNat = f.list.dst0 from UInt32.toNat_ofNat_of_lt' hd,
    show f.list.src0.toUInt32.toNat = f.list.src0 from UInt32.toNat_ofNat_of_lt' hs]
  exact h.2.2

theorem published_composer (g : Geom) (pin : Bool) (over bf bn height : Nat)
    (h : g.composerTop < UInt32.size) :
    (make g pin over bf bn height).words[10]!.toNat = g.composerTop := by
  have hw (f : Frame) : f.words[10]! = f.composer.dst0.toUInt32 := by
    simp [Frame.words, Rect.words]
  rw [hw]
  exact UInt32.toNat_ofNat_of_lt' h

theorem row_place (g : Geom) (over bf bn height r : Nat) :
    (make g false over bf bn height).row r = Seam.place g over bf bn r := by
  simp [make, Frame.row, Seam.place]; omega

theorem row_pinned (g : Geom) (over bf bn height r : Nat) :
    (make g true over bf bn height).row r = Seam.pinned g over r := by
  simp [make, Frame.row, Seam.pinned]

theorem placed_row (g : Geom) (hf : g.Fits) (over bf bn height r : Nat) :
    (make g false over bf bn height).row r = Seam.home g bn (Seam.frameRow g over bf r) := by
  rw [row_place]; exact Geometry.placed_row g hf over bf bn r

/-- The published rectangle copies every visible buffer row to its home. -/
theorem visible_in_viewport (g : Geom) (hf : g.Fits) (over bf bn height r : Nat)
    (hr : r < height) (lo : (bn : Int) ≤ Seam.frameRow g over bf r)
    (hi : Seam.frameRow g over bf r < bn + g.viewNow) :
    let f := make g false over bf bn height
    f.list.src0 ≤ r ∧ r < f.list.src1 ∧
    (f.list.dst0 : Int) + (r - f.list.src0 : Nat) = Seam.home g bn (Seam.frameRow g over bf r) := by
  have hv := Geometry.visible_in_viewport g hf bn (Seam.frameRow g over bf r) lo hi
  have hp := placed_row g hf over bf bn height r
  change (make g false over bf bn height).origin + r = _ at hp
  have hc := crop_row (make g false over bf bn height).origin height g.top g.composerTop r hr
    (by rw [hp]; exact hv.1) (by rw [hp]; exact hv.2)
  exact ⟨hc.1, hc.2.1, hc.2.2.trans hp⟩

theorem pinned_row (g : Geom) (over bf bn height r : Nat) :
    (make g true over bf bn height).row r = (g.top : Int) + Seam.pageRow over r := by
  rw [row_pinned]; exact Geometry.pinned_row g over r

theorem pinned_visible (g : Geom) (over bf bn height k : Nat) (hk : k < g.viewNow) :
    (g.top : Int) ≤ (make g true over bf bn height).row (over + k) ∧
    (make g true over bf bn height).row (over + k) < g.composerTop := by
  rw [row_pinned]; exact Geometry.pinned_visible g over k hk

theorem newest_drawn (g : Geom) (hf : g.Fits) (over pad h height r : Nat)
    (fit : pad + h ≤ g.viewNow) (hr : Seam.frameRow g over 0 r = pad + h - 1) (hh : 0 < h) :
    (g.top : Int) ≤ (make g false over 0 0 height).row r ∧
    (make g false over 0 0 height).row r < g.composerTop := by
  rw [row_place]; exact Geometry.newest_drawn g hf over pad h fit r hr hh

theorem offset_bounds (maxB : Nat) (sample : Int) :
    0 ≤ offset maxB sample ∧ offset maxB sample ≤ maxB :=
  ⟨Nat.zero_le _, Nat.min_le_right _ _⟩
end Surface
