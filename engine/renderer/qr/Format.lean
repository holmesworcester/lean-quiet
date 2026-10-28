/-
Format and version information: BCH codes around the finder patterns.

Format information is 5 bits (the level's two bits and the mask's three)
and a BCH(15,5) remainder, XORed with 0x5412. Version information (versions
7 to 40) is 6 bits and a BCH(18,6) remainder. Both codes keep distinct
codewords at least 7 (format) and 8 (version) bits apart, so a reading with
at most 3 wrong bits is nearer to its codeword than to any other: the
decoders take the codeword within distance 3, and that is the one written
(`decodeFormat_correct`, `decodeVersion_correct`, proven).
-/
import engine.renderer.qr.Tables

namespace Qr

/-- Bits where `a` and `b` differ among their low `k`. -/
def hd (k a b : Nat) : Nat := (List.range k).countP fun i => a.testBit i != b.testBit i

/-- The 15 format bits of 5 data bits. -/
def bchFormat (d : Nat) : Nat :=
  let r := (List.range 10).foldl (fun r _ => (r <<< 1) ^^^ ((r >>> 9) * 0x537)) d
  ((d <<< 10) ||| r) ^^^ 0x5412

/-- The 18 version bits of a version. -/
def bchVersion (v : Nat) : Nat :=
  let r := (List.range 12).foldl (fun r _ => (r <<< 1) ^^^ ((r >>> 11) * 0x1F25)) v
  (v <<< 12) ||| r

def formatData (e : Ecc) (mask : Nat) : Nat := e.bits * 8 + mask % 8

def formatBits (e : Ecc) (mask : Nat) : Nat := bchFormat (formatData e mask)

/-- The format data (level bits and mask) whose codeword is within 3 bits
of `x`. -/
def decodeFormatData (x : Nat) : Option Nat :=
  (List.range 32).find? fun d => hd 15 (bchFormat d) x ≤ 3

def decodeFormat (x : Nat) : Option (Ecc × Nat) :=
  (decodeFormatData x).map fun d => (Ecc.ofBits (d / 8), d % 8)

/-- The version (7 to 40) whose codeword is within 3 bits of `x`. -/
def decodeVersion (x : Nat) : Option Nat :=
  (List.range' 7 34).find? fun v => hd 18 (bchVersion v) x ≤ 3

/-! ## Laws -/

theorem countP_triangle {α : Type} (p q r : α → Bool) (h : ∀ x, p x → q x ∨ r x) :
    ∀ l : List α, l.countP p ≤ l.countP q + l.countP r
  | [] => by simp
  | x :: l => by
    have ih := countP_triangle p q r h l
    simp only [List.countP_cons]
    have := h x
    cases hp : p x <;> cases hq : q x <;> cases hr : r x <;> simp_all <;> omega

theorem hd_triangle (k a b c : Nat) : hd k a c ≤ hd k a b + hd k b c := by
  apply countP_triangle
  intro i
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> simp

theorem hd_comm (k a b : Nat) : hd k a b = hd k b a := by
  unfold hd; congr 1; funext i; cases a.testBit i <;> cases b.testBit i <;> rfl

theorem find?_unique {α : Type} (p : α → Bool) (x : α) :
    ∀ (l : List α), x ∈ l → p x = true → (∀ y ∈ l, p y = true → y = x) → l.find? p = some x
  | [], hx, _, _ => by simp at hx
  | y :: l, hx, hp, hu => by
    simp only [List.find?_cons]
    cases hy : p y
    · simp only
      have : x ∈ l := by
        rcases List.mem_cons.mp hx with rfl | h
        · simp [hp] at hy
        · exact h
      exact find?_unique p x l this hp (fun z hz hpz => hu z (by simp [hz]) hpz)
    · simp only [hu y (by simp) hy]

/-- Distinct format codewords differ in at least 7 bits. -/
theorem format_distance : ∀ a, a < 32 → ∀ b, b < 32 → a ≠ b → 7 ≤ hd 15 (bchFormat a) (bchFormat b) := by
  decide +kernel

/-- Distinct version codewords differ in at least 8 bits. -/
theorem version_distance : ∀ a, a < 34 → ∀ b, b < 34 → a ≠ b →
    8 ≤ hd 18 (bchVersion (a + 7)) (bchVersion (b + 7)) := by
  decide +kernel

/-- A format reading with at most 3 wrong bits decodes to what was
written. -/
theorem decodeFormatData_correct {d x : Nat} (hd32 : d < 32) (h : hd 15 (bchFormat d) x ≤ 3) :
    decodeFormatData x = some d := by
  apply find?_unique _ d _ (by simp [hd32]) (by simp [h])
  intro y hy hp
  simp only [List.mem_range] at hy
  simp only [decide_eq_true_eq] at hp
  by_cases hne : y = d
  · exact hne
  have h7 := format_distance y hy d hd32 hne
  have t := hd_triangle 15 (bchFormat y) x (bchFormat d)
  rw [hd_comm 15 x] at t
  omega

theorem ofBits_bits (e : Ecc) : Ecc.ofBits e.bits = e := by cases e <;> rfl

theorem decodeFormat_correct {e : Ecc} {mask x : Nat} (hm : mask < 8)
    (h : hd 15 (formatBits e mask) x ≤ 3) : decodeFormat x = some (e, mask) := by
  have hb : e.bits < 4 := by cases e <;> decide
  unfold decodeFormat
  rw [decodeFormatData_correct (by unfold formatData; omega) h]
  simp only [Option.map_some, formatData, Option.some.injEq, Prod.mk.injEq]
  refine ⟨?_, by omega⟩
  rw [show (e.bits * 8 + mask % 8) / 8 = e.bits by omega, ofBits_bits]

/-- A version reading with at most 3 wrong bits decodes to what was
written. -/
theorem decodeVersion_correct {v x : Nat} (h7 : 7 ≤ v) (h40 : v ≤ 40)
    (h : hd 18 (bchVersion v) x ≤ 3) : decodeVersion x = some v := by
  apply find?_unique _ v _ (by simp [List.mem_range'_1]; omega) (by simp [h])
  intro y hy hp
  simp only [List.mem_range'] at hy
  simp only [decide_eq_true_eq] at hp
  obtain ⟨i, hi, rfl⟩ := hy
  by_cases hne : 7 + 1 * i = v
  · exact hne
  have h8 := version_distance i hi (v - 7) (by omega) (by omega)
  rw [show v - 7 + 7 = v by omega] at h8
  have t := hd_triangle 18 (bchVersion (i + 7)) x (bchVersion v)
  rw [hd_comm 18 x] at t
  simp only [show 7 + 1 * i = i + 7 by omega] at hp
  omega

end Qr
