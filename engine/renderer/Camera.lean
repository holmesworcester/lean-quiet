/-
The camera's preview on Join with QR code, drawn by the app from the
frames it decodes (the twin hands over Y planes only): the frame turned
upright by the sensor's orientation, its centre square, scaled to the
page's square, in grey.

`src` says which frame pixel a preview pixel shows. Law: `src_in` (every
preview pixel reads inside the frame: no index past its bytes, whatever
the frame's size, stride or orientation, as long as the frame holds its
rows).
-/
import engine.renderer.Paint

namespace Camera
open Paint

/-- A frame as the twin gives it: Y plane, size, stride, and the sensor's
clockwise orientation in degrees. -/
structure Frame where
  w : Nat
  h : Nat
  stride : Nat
  orient : Nat
  px : ByteArray

/-- Quarter turns clockwise (0-3) that make the frame upright. -/
def Frame.turns (f : Frame) : Nat := f.orient / 90 % 4

/-- The frame's size upright (a quarter turn swaps its sides). -/
def Frame.upright (f : Frame) : Nat × Nat :=
  if f.turns % 2 = 1 then (f.h, f.w) else (f.w, f.h)

/-- The frame pixel (x, y) that preview pixel (i, j) of an S-square shows:
the upright frame's centre square of side m = min of its sides, scaled. -/
def src (f : Frame) (S i j : Nat) : Nat × Nat :=
  let (uw, uh) := f.upright
  let m := min uw uh
  -- (u, v) in the upright frame
  let u := (uw - m) / 2 + i * m / S
  let v := (uh - m) / 2 + j * m / S
  if f.turns = 1 then (v, f.h - 1 - u)
  else if f.turns = 2 then (f.w - 1 - u, f.h - 1 - v)
  else if f.turns = 3 then (f.w - 1 - v, u)
  else (u, v)

theorem scaled_lt (m S i : Nat) (hi : i < S) (hm : 0 < m) : i * m / S < m := by
  have hS : 0 < S := by omega
  rw [Nat.div_lt_iff_lt_mul hS, Nat.mul_comm m S]
  exact Nat.mul_lt_mul_of_pos_right hi hm

/-- **Every preview pixel reads inside the frame.** -/
theorem src_in (f : Frame) (S i j : Nat) (hi : i < S) (hj : j < S) (hw : 0 < f.w) (hh : 0 < f.h) :
    (src f S i j).1 < f.w ∧ (src f S i j).2 < f.h := by
  have ht : f.turns < 4 := Nat.mod_lt _ (by decide)
  unfold src Frame.upright
  by_cases ho : f.turns % 2 = 1
  · simp only [ho, ite_true]
    have a := scaled_lt (min f.h f.w) S i hi (by omega)
    have b := scaled_lt (min f.h f.w) S j hj (by omega)
    generalize i * min f.h f.w / S = x at *
    generalize j * min f.h f.w / S = y at *
    repeat' split
    all_goals simp only []
    all_goals omega
  · simp only [ho, ite_false]
    have a := scaled_lt (min f.w f.h) S i hi (by omega)
    have b := scaled_lt (min f.w f.h) S j hj (by omega)
    generalize i * min f.w f.h / S = x at *
    generalize j * min f.w f.h / S = y at *
    repeat' split
    all_goals simp only []
    all_goals omega

/-- The preview, S pixels square, sampled every other pixel each way (a
camera preview needs no more, and the page repaints at the camera's rate).
A frame too short for its rows shows black. -/
def preview (f : Frame) (S : Nat) : Bitmap := Id.run do
  let ok := f.w > 0 && f.h > 0 && f.stride ≥ f.w && f.px.size ≥ f.stride * f.h
  let mut rows := Array.emptyWithCapacity S
  for j2 in [0:(S + 1) / 2] do
    let mut row := solid 0 S
    if ok then
      for i2 in [0:(S + 1) / 2] do
        let (x, y) := src f S (2 * i2) (2 * j2)
        let g := (f.px[y * f.stride + x]!).toNat
        let c := (g * 0x10101).toUInt32
        row := setPx (setPx row (2 * i2) c) (2 * i2 + 1) c
    rows := rows.push row
    if rows.size < S then rows := rows.push row
  return { w := S, rows := rows }

end Camera
