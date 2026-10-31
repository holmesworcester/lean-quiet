import engine.renderer.Surface
import engine.renderer.Camera
import engine.renderer.SheetGeom
import engine.renderer.Cover
import engine.renderer.SlideLaws

/-! A portrait viewport with the keyboard visible, a scrolled emoji grid,
and a twelve-pixel camera plane. Inputs are synthetic, fully concrete;
no viewport or hit-box premise is supplied as a hypothesis. -/
namespace Vacuity.RendererGeometry

def phone : Geometry.Geom := ⟨1280, 24, 300, 80, 100⟩
private theorem fits : phone.Fits := by unfold Geometry.Geom.Fits; decide

-- The frame is drawn at offset 100, then displayed after a 24px scroll.
theorem placed : (Surface.make phone false 8 100 124 1200).row 600 =
    Geometry.Seam.home phone 124 (Geometry.Seam.frameRow phone 8 100 600) :=
  Surface.placed_row phone fits 8 100 124 1200 600
example : (Surface.make phone false 8 100 124 1200).row 600 = 420 := by decide

theorem visible :
    let f := Surface.make phone false 8 100 124 1200
    f.list.src0 ≤ 600 ∧ 600 < f.list.src1 ∧
    (f.list.dst0 : Int) + (600 - f.list.src0 : Nat) =
      Geometry.Seam.home phone 124 (Geometry.Seam.frameRow phone 8 100 600) :=
  Surface.visible_in_viewport phone fits 8 100 124 1200 600 (by decide) (by decide) (by decide)

theorem newest : (phone.top : Int) ≤ Geometry.Seam.home phone 0 (12 + 47) ∧
    Geometry.Seam.home phone 0 (12 + 47) < phone.composerTop :=
  Geometry.newest_visible phone fits 12 48 (by decide) 47 (by decide)

theorem newestDrawn :
    (phone.top : Int) ≤ (Surface.make phone false 8 0 0 1200).row 1024 ∧
    (Surface.make phone false 8 0 0 1200).row 1024 < phone.composerTop :=
  Surface.newest_drawn phone fits 8 12 48 1200 1024 (by decide) (by decide) (by decide)

theorem pinnedRow : (Surface.make phone true 8 100 124 1200).row 128 =
    (phone.top : Int) + Geometry.Seam.pageRow 8 128 :=
  Surface.pinned_row phone 8 100 124 1200 128

theorem pinnedVisible :
    (phone.top : Int) ≤ (Surface.make phone true 8 100 124 1200).row (8 + 120) ∧
    (Surface.make phone true 8 100 124 1200).row (8 + 120) < phone.composerTop :=
  Surface.pinned_visible phone 8 100 124 1200 120 (by decide)

theorem pageTap : Geometry.Seam.tapRow phone 200 = (200 : Int) - phone.top :=
  Geometry.pinned_tap phone fits 200
example : Geometry.Seam.tapRow phone 200 = 120 := by decide
example : ¬ (Geometry.Geom.mk 400 24 300 80 100).Fits := by unfold Geometry.Geom.Fits; decide
example : ¬ 900 < phone.viewNow := by decide

def grid : SheetGeom.Grid := ⟨8, 100, 48, 40, 6, 120, 100⟩
private theorem gridOk : grid.Ok := ⟨by decide, by decide, by decide⟩
private theorem inKey : grid.inBox 160 30 20 148 := by unfold SheetGeom.Grid.inBox; decide

theorem hit : grid.hit 160 20 148 = some 30 ↔ 30 < grid.n ∧ grid.inBox 160 30 20 148 :=
  SheetGeom.hit_iff grid gridOk 160 20 148 30

theorem hitCell : grid.hit 160 20 148 = some 30 :=
  SheetGeom.hit_cell grid gridOk 160 30 20 148 (by decide) inKey
example : grid.hit 160 50 148 = none := by decide -- gap between keys
example : grid.hit 160 20 220 = none := by decide -- below visible grid
example : ¬ grid.inBox 160 31 20 148 := by unfold SheetGeom.Grid.inBox; decide -- adjacent key cannot own tap

-- The same concrete tap cannot belong to any distinct valid key.
theorem disjoint : ∀ i, i < grid.n → grid.inBox 160 i 20 148 → i = 30 := by
  intro i hi hbox
  exact SheetGeom.keys_disjoint grid gridOk 160 i 30 20 148 hi (by decide) hbox inKey

theorem reachable : ∃ s, s ≤ grid.maxScroll ∧ s ≤ grid.ctop 99 ∧
    grid.ctop 99 + grid.key ≤ s + grid.vh :=
  SheetGeom.reachable grid gridOk (by decide) 99 (by decide)
example : grid.maxScroll = 560 ∧ grid.ctop 99 = 640 := by decide

theorem item : grid.itemAt 5 2 / grid.cols = 5 ∧ grid.itemAt 5 2 % grid.cols = 2 :=
  SheetGeom.itemAt_place grid gridOk (by decide)
theorem line : grid.lineOf 208 = (30 / grid.cols, 208 - grid.ctop 30) :=
  SheetGeom.lineOf_ctop grid gridOk 30 208 (by decide) (by decide)

theorem composeRow : (SheetGeom.compose #[10, 11] (fun n : Nat => n + 100) 3 20 #[99])[3] = 121 :=
  SheetGeom.compose_row #[10, 11] (fun n : Nat => n + 100) 3 20 #[99] 1 (by decide) (by decide)
theorem composeTop : (SheetGeom.compose #[10, 11] (fun n : Nat => n + 100) 3 20 #[99])[1] = 11 :=
  SheetGeom.compose_top #[10, 11] (fun n : Nat => n + 100) 3 20 #[99] 1 (by decide) (by decide)

def camera (degrees : Nat) : Camera.Frame :=
  ⟨4, 3, 4, degrees, ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩
theorem cameraBounds :
    ((Camera.src (camera 0) 3 2 1).1 < 4 ∧ (Camera.src (camera 0) 3 2 1).2 < 3) ∧
    ((Camera.src (camera 90) 3 2 1).1 < 4 ∧ (Camera.src (camera 90) 3 2 1).2 < 3) ∧
    ((Camera.src (camera 180) 3 2 1).1 < 4 ∧ (Camera.src (camera 180) 3 2 1).2 < 3) ∧
    ((Camera.src (camera 270) 3 2 1).1 < 4 ∧ (Camera.src (camera 270) 3 2 1).2 < 3) :=
  ⟨Camera.src_in _ _ _ _ (by decide) (by decide) (by decide) (by decide),
   Camera.src_in _ _ _ _ (by decide) (by decide) (by decide) (by decide),
   Camera.src_in _ _ _ _ (by decide) (by decide) (by decide) (by decide),
   Camera.src_in _ _ _ _ (by decide) (by decide) (by decide) (by decide)⟩
example : Camera.src (camera 90) 3 2 1 = (1, 0) ∧
    Camera.src (camera 270) 3 2 1 = (2, 2) := by decide
example : ¬ 3 < (3 : Nat) := by decide -- preview index on edge violates premise

-- Loaded painted row, pending row, and positions outside the window.
def rows : List (Nat × Option Nat) := [(48, some 48), (72, none)]
theorem coverage : Cover.seen 12 20 false rows 35 ≠ .blank :=
  Cover.covered 12 20 false rows 35 (by decide) (by decide)
theorem painted : ∃ hj bh, rows[0]? = some (hj, some bh) ∧ 32 < bh :=
  Cover.line_painted 12 20 false rows 35 0 32 (by decide)
example : Cover.seen 12 20 false rows 35 = .line 0 32 := by decide
example : Cover.seen 12 20 false rows 80 = .hold 1 := by decide
example : Cover.seen 12 20 true rows 160 = .unloaded := by decide
example : Cover.seen 12 20 false rows 160 = .blank := by decide
example : Cover.seen 12 20 false rows 4 = .blank := by decide

-- Translated buffer crop and the fixed-width ABI at a nonzero scroll.
theorem translation :
    Translate.row (Surface.make phone false 8 100 124 1200) 148 600 =
      Geometry.Seam.place phone 8 100 148 600 :=
  Translate.equivariance phone 8 100 124 148 1200 600

theorem slide : Slide.edge false 2 false 100 (-204) 1200 80 880 148 =
    Translate.edge false 2 false 100 (-204) 1200 80 880 148 :=
  Slide.edge_eq false 2 false 100 (-204) 1200 80 880 148

-- A translated painted frame and the placeholder fill share the same content.
def chatFrame := Surface.make (Geometry.Geom.mk 200 0 0 20 20) false 8 100 100 176

theorem translatedCoverage : Translate.seen chatFrame 176 268 0 0 false
    [(500, some 500)] 100 20 ≠ .blank :=
  Translate.covered chatFrame 176 268 0 0 false [(500, some 500)] 100 20 (by
    intro r hr
    constructor
    · exact Nat.zero_le _
    · left
      have hs : Translate.source chatFrame.pin chatFrame.b chatFrame.origin 100 176 20 = some 8 := by decide
      rw [hs] at hr
      cases hr
      decide)

def placeholder : Hold.St := { bgRow := ByteArray.mk #[255, 255, 255, 255], dim := default, W := 1 }

theorem fillPixel :
    (Hold.plane placeholder (180 - 20))[
      (Translate.fillRow false 100 20 180 (-500) 40).toNat]! =
    Hold.holdLine placeholder (Translate.content (-500) 180 40 % 48).toNat :=
  Translate.fill_pixel placeholder 100 20 180 (-500) 40 (by decide) (by decide) (by decide)

end Vacuity.RendererGeometry
