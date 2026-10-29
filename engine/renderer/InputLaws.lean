/- Laws of the classifier, mapper and event fold used by Session.present.
The witnesses use real geometry with a keyboard and a visible page/key. -/
import engine.renderer.Input
namespace Input
open Geometry

theorem moved_not_tap (p : Press) (time : Nat) (h : p.context.slop < p.travel) :
    classify p time = none := by simp [classify, h]

theorem release_tap (p : Press) (time : Nat) (hm : p.travel ≤ p.context.slop)
    (hh : p.held = false) (ht : time - p.first.time < 500) :
    classify p time = some (.tap p.first.pos) := by
  simp [classify, Nat.not_lt.mpr hm, hh, ht]

theorem sample_remembers (p : Press) (t : Touch) :
    p.travel ≤ (p.sample t).travel ∧ distance p.first.pos t.pos ≤ (p.sample t).travel :=
  ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

theorem release_moved (p : Press) (t : Touch)
    (h : p.context.slop < distance p.first.pos t.pos) :
    classify (p.sample t) t.time = none := by
  apply moved_not_tap
  exact Nat.lt_of_lt_of_le h (sample_remembers p t).2

theorem first_pointer (s : State) (p : Press) (t : Touch) (h : t.id ≠ p.first.id) :
    follow s p t = ⟨s, [], []⟩ := by simp [follow, h]

theorem extra_down (c : Context) (s : State) (t : Touch)
    (hd : t.phase = 0) (hs : s.pointers.isEmpty = false) :
    (touch c s t).state.press = s.press ∧ (touch c s t).events = [] ∧
      (touch c s t).motion = [] := by simp [touch, hd, hs]

theorem other_pointer (c : Context) (s : State) (p : Press) (t : Touch)
    (hp : s.press = some p) (hd : t.phase ≠ 0) (hi : t.id ≠ p.first.id) :
    (touch c s t).state.press = s.press ∧ (touch c s t).events = [] ∧
      (touch c s t).motion = [] := by simp [touch, hd, hp, follow, hi]

/-- The event the app receives contains the mapped DOWN coordinates. -/
theorem release_event (s : State) (p : Press) (t : Touch)
    (hi : t.id = p.first.id) (hu : t.phase = 2)
    (hm : (p.sample t).travel ≤ p.context.slop) (hh : p.held = false)
    (ht : t.time - p.first.time < 500) :
    deliver p.context.frame (.tap p.first.pos) ∈ (follow s p t).events := by
  have hc := release_tap (p.sample t) t.time hm hh ht
  change classify (p.sample t) t.time = some (.tap p.first.pos) at hc
  simp [follow, hi, hu, hc]

/-- A release from a revoked mount cannot act on its replacement. -/
theorem revoked_release (c : Context) (s : State) (t : Touch) (up : 2 ≤ t.phase) :
    (touch c (revoke s) t).events = [] := by
  simp [touch, revoke, show t.phase ≠ 0 by omega]

/-- Same initial state, frame and raw sequence produce identical results. -/
theorem deterministic (c : Context) (s s' : State) (es es' : List Raw)
    (hs : s = s') (he : es = es') : run c s es = run c s' es' := by rw [hs, he]

theorem step_offset (c : Context) (s : State) (e : Raw) :
    (step c s e).state.offset ≤ c.maxB := (Surface.offset_bounds _ _).2

theorem sequence_offset (c : Context) (s : State) (es : List Raw) :
    0 ≤ (run c s es).state.offset ∧ (run c s es).state.offset ≤ c.maxB := by
  constructor
  · exact Nat.zero_le _
  · unfold run
    generalize h : (Result.mk { s with offset := Surface.offset c.maxB s.offset } [] []) = r
    have hr : r.state.offset ≤ c.maxB := by
      rw [← h]; exact (Surface.offset_bounds _ _).2
    clear h
    induction es generalizing r with
    | nil => exact hr
    | cons e es ih =>
      simp only [List.foldl_cons]
      apply ih
      exact step_offset c r.state e

/-- Inverse of the actual conversation placement, at the down position. -/
theorem tap_content (g : Geom) (_hf : g.Fits) (over bf bn height y : Nat) :
    Seam.home g bn (content (Surface.make g false over bf bn height) y) = y := by
  simp [content, Surface.make, Seam.home]; omega

/-- Page-coordinate conversion is exactly pinned_tap's conversion. -/
theorem tap_page (g : Geom) (hf : g.Fits) (over bf bn height y : Nat) :
    (g.view : Int) - 1 - content (Surface.make g true over bf bn height) y =
      (y : Int) - g.top := by
  change Seam.tapRow g y = _
  exact Geometry.pinned_tap g hf y

/-- Composer coordinates used by deliver feed the proved grid hit. -/
theorem tap_key (f : Surface.Frame) (grid : SheetGeom.Grid) (ok : grid.Ok)
    (scroll i : Nat) (p : Point) :
    (match deliver f (.tap p) with
      | .tap _ x y => grid.hit scroll x.toNat y.toNat
      | _ => none) = some i ↔
      i < grid.n ∧ grid.inBox scroll i p.x.toNat.toUInt32.toNat (coord f p).toUInt32.toNat :=
  SheetGeom.hit_iff grid ok scroll p.x.toNat.toUInt32.toNat (coord f p).toUInt32.toNat i

/-- Classification never substitutes the release position for the down. -/
theorem classified_at_down (p : Press) (time : Nat) (q : Point)
    (h : classify p time = some (.tap q)) : q = p.first.pos := by
  unfold classify at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

theorem classified_page (p : Press) (time : Nat) (q : Point)
    (_h : classify p time = some (.tap q))
    (pin : p.context.frame.pin = true) (fit : p.context.frame.g.Fits) (hy : 0 ≤ q.y) :
    (p.context.frame.g.view : Int) - 1 - content p.context.frame q.y = q.y - p.context.frame.g.top := by
  have ht := Geometry.pinned_tap p.context.frame.g fit q.y.toNat
  simp only [Seam.tapRow, Int.toNat_of_nonneg hy] at ht
  simpa [content, pin] using ht

/-- A classified tap uses hit_iff on exactly the coordinates deliver sends. -/
theorem classified_key (p : Press) (time : Nat) (q : Point)
    (h : classify p time = some (.tap q)) (grid : SheetGeom.Grid) (ok : grid.Ok)
    (scroll i : Nat) :
    (match deliver p.context.frame (.tap q) with
      | .tap _ x y => grid.hit scroll x.toNat y.toNat
      | _ => none) = some i ↔
      i < grid.n ∧ grid.inBox scroll i p.first.pos.x.toNat.toUInt32.toNat (coord p.context.frame p.first.pos).toUInt32.toNat := by
  rw [classified_at_down p time q h]
  exact tap_key p.context.frame grid ok scroll i p.first.pos

/-- The actual delivered page event decodes to the drawn page row. -/
theorem delivered_page (g : Geom) (fit : g.Fits) (over height x y : Nat)
    (lo : g.top ≤ y) (hi : y < g.composerTop) (hw : g.view < UInt32.size) :
    let f := Surface.make g true over 0 0 height
    match deliver f (.tap ⟨x, y⟩) with
    | .tap .list _ distance => g.view - 1 - distance.toNat = y - g.top
    | _ => False := by
  have hp := Geometry.pinned_tap g fit y
  have hs := Geometry.view_shift g fit
  have hv : (content (Surface.make g true over 0 0 height) y).toNat < UInt32.size := by
    simp only [content, Surface.make, ite_true]
    unfold Geom.view Geom.composerTop Geom.shift Geom.Fits at *
    omega
  have nlo : ¬ (y : Int) < g.top := by omega
  have nhi : ¬ (y : Int) ≥ g.composerTop := by omega
  simp only [deliver, coord, region, Surface.make, nlo, nhi, ite_false, content, ite_true]
  rw [show ((g.composerTop : Int) + g.shift - 1 - y).toNat.toUInt32.toNat =
      ((g.composerTop : Int) + g.shift - 1 - y).toNat from UInt32.toNat_ofNat_of_lt' hv]
  unfold Geom.view Geom.composerTop Geom.shift Geom.Fits at *
  omega

/-- A concrete keyboard-open geometry, tap and drag satisfy the premises. -/
theorem witnesses :
    let g : Geom := ⟨800, 20, 300, 80, 60⟩
    let c : Context := ⟨Surface.make g true 32 0 0 704, 160, 100⟩
    let p : Press := ⟨⟨0, 7, ⟨100, 120⟩, 1000⟩, c, 3, false⟩
    g.Fits ∧ classify p 1100 = some (.tap ⟨100, 120⟩) ∧
      classify (p.sample ⟨1, 7, ⟨120, 120⟩, 1100⟩) 1200 = none ∧
      (g.view : Int) - 1 - content c.frame 120 = 40 := by exact ⟨by unfold Geom.Fits; decide, rfl, rfl, rfl⟩
end Input
