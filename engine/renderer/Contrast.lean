/-
WCAG 2.x sRGB luminance. Each table entry is a lower bound in millionths;
the next integer is an upper bound. `channel_bounds` checks the 12/5
power by integer fifth powers, with no Float or native_decide axiom.
`ink` reads the already composited pixel under a glyph. It keeps the
requested palette ink when it passes, otherwise uses black or white.
The conservative test includes the rounding error in the denominator.
-/
import engine.renderer.Palette

namespace Contrast
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

private def channels : Array Nat := #[
  0, 303, 607, 910, 1214, 1517, 1821, 2124, 2428, 2731, 3035, 3346, 3676, 4024, 4391, 4776,
  5181, 5605, 6048, 6512, 6995, 7499, 8023, 8568, 9134, 9721, 10329, 10960, 11612, 12286, 12983, 13702,
  14443, 15208, 15996, 16807, 17641, 18500, 19382, 20288, 21219, 22173, 23153, 24157, 25186, 26241, 27320, 28426,
  29556, 30713, 31896, 33104, 34339, 35601, 36889, 38204, 39546, 40915, 42311, 43735, 45186, 46665, 48171, 49706,
  51269, 52860, 54480, 56128, 57805, 59511, 61246, 63010, 64803, 66625, 68478, 70360, 72271, 74213, 76185, 78187,
  80219, 82282, 84376, 86500, 88655, 90841, 93058, 95307, 97587, 99898, 102241, 104616, 107023, 109461, 111932, 114435,
  116970, 119538, 122138, 124771, 127437, 130136, 132868, 135633, 138431, 141263, 144128, 147027, 149959, 152926, 155926, 158960,
  162029, 165132, 168269, 171441, 174647, 177888, 181164, 184474, 187820, 191201, 194617, 198069, 201556, 205078, 208636, 212230,
  215860, 219526, 223227, 226965, 230740, 234550, 238397, 242281, 246201, 250158, 254152, 258182, 262250, 266355, 270497, 274677,
  278894, 283148, 287440, 291770, 296138, 300543, 304987, 309468, 313988, 318546, 323143, 327778, 332451, 337163, 341914, 346704,
  351532, 356400, 361306, 366252, 371237, 376262, 381326, 386429, 391572, 396755, 401977, 407240, 412542, 417885, 423267, 428690,
  434153, 439657, 445201, 450785, 456411, 462076, 467783, 473531, 479320, 485149, 491020, 496932, 502886, 508881, 514917, 520995,
  527115, 533276, 539479, 545724, 552011, 558340, 564711, 571124, 577580, 584078, 590618, 597201, 603827, 610495, 617206, 623960,
  630757, 637596, 644479, 651405, 658374, 665387, 672443, 679542, 686685, 693871, 701101, 708375, 715693, 723055, 730460, 737910,
  745404, 752942, 760524, 768151, 775822, 783537, 791297, 799102, 806952, 814846, 822785, 830769, 838799, 846873, 854992, 863157,
  871367, 879622, 887923, 896269, 904661, 913098, 921581, 930110, 938685, 947306, 955973, 964686, 973445, 982250, 991102, 1000000]

def linear (c : UInt8) : Nat := channels[c.toNat]!

/-- Integer certificate for sRGB's linear branch and its 2.4 power. -/
def channelBound (c : UInt8) : Prop :=
  let v := linear c
  let n := c.toNat
  if n ≤ 10 then
    v * 82365 ≤ n * 25000000 ∧ n * 25000000 ≤ (v + 1) * 82365
  else
    v^5 * 53805^12 ≤ (200*n + 2805)^12 * 1000000^5 ∧
    (200*n + 2805)^12 * 1000000^5 ≤ (v+1)^5 * 53805^12

instance (c : UInt8) : Decidable (channelBound c) := by unfold channelBound; infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- All 256 channel intervals enclose the WCAG transfer function. -/
theorem channel_bounds : ∀ c : Fin 256, channelBound c.val.toUInt8 := by decide

/-- Luminance in ten-billionths; the upper bound is this plus 10000. -/
def luminance (c : UInt32) : Nat :=
  2126 * linear (c >>> 16).toUInt8 + 7152 * linear (c >>> 8).toUInt8 + 722 * linear c.toUInt8

/-- Conservative contrast test, ratio in tenths (45 body; 30 controls). -/
def meets (a b : UInt32) (ratio : Nat := 45) : Prop :=
  10 * (max (luminance a) (luminance b) + 500000000) ≥
    ratio * (min (luminance a) (luminance b) + 500010000)

instance (a b : UInt32) (n : Nat) : Decidable (meets a b n) := by unfold meets; infer_instance

/-- Resolve ink on the actual composited ground, retaining the palette
choice whenever it meets the body-text minimum. -/
def ink (wanted ground : UInt32) : UInt32 :=
  if meets wanted ground then wanted
  else if luminance ground ≥ 1800000000 then Palette.color .light .black
  else Palette.color .light .white

private theorem black_lum : luminance (Palette.color .light .black) = 0 := by decide
private theorem white_lum : luminance (Palette.color .light .white) = 10000000000 := by decide

private theorem dark_ground (g : Nat) (h : g < 1800000000) :
    10 * (max 10000000000 g + 500000000) ≥ 45 * (min 10000000000 g + 500010000) := by
  rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
  omega

private theorem light_ground (g : Nat) (h : 1800000000 ≤ g) :
    10 * (max 0 g + 500000000) ≥ 45 * (min 0 g + 500010000) := by
  simp only [Nat.zero_max, Nat.zero_min]
  omega

private theorem weaker (a b : Nat)
    (h : 10 * (max a b + 500000000) ≥ 45 * (min a b + 500010000)) :
    10 * (max a b + 500000000) ≥ 30 * (min a b + 500010000) :=
  Nat.le_trans (Nat.mul_le_mul_right _ (by decide : 30 ≤ 45)) h

/-- Every resolved text pixel meets 4.5:1 against the pixel it replaces. -/
theorem ink_meets (wanted ground : UInt32) : meets (ink wanted ground) ground := by
  unfold ink
  split
  · assumption
  · split
    · unfold meets
      rw [black_lum]
      exact light_ground _ (by assumption)
    · unfold meets
      rw [white_lum]
      exact dark_ground _ (Nat.lt_of_not_ge (by assumption))

/-- The same resolved ink also meets the 3:1 non-text minimum. -/
theorem ink_control (wanted ground : UInt32) : meets (ink wanted ground) ground 30 :=
  weaker _ _ (ink_meets wanted ground)

/-- A passing palette ink is kept byte for byte. -/
theorem ink_kept (wanted ground : UInt32) (h : meets wanted ground) :
    ink wanted ground = wanted := by simp [ink, h]

/-- Non-vacuity: libquiet's light foreground on its panel passes, so
the branch that preserves the requested palette ink really is used. -/
theorem possible : meets (Palette.color .light .fg) (Palette.color .light .panel) ∧
    ink (Palette.color .light .fg) (Palette.color .light .panel) = Palette.color .light .fg :=
  ⟨by decide, ink_kept _ _ (by decide)⟩

end Contrast
