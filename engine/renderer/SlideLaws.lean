/- The fixed-width exports equal the original integer functions on the
entire ABI domain. No pixel-sized input can overflow the UInt64 bias.
The four equalities transfer all existing Translate laws unchanged. -/
import engine.renderer.TranslateLaws
namespace Slide

private theorem add_nat (a b : UInt64) (h : a.toNat + b.toNat < 18446744073709551616) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [UInt64.toNat_add, Nat.reducePow, Nat.mod_eq_of_lt h]

private theorem sub_nat (a b : UInt64) : (sub a b).toNat = a.toNat - b.toNat := by
  unfold sub
  split
  · simp_all [UInt64.lt_iff_toNat_lt]; omega
  · next h =>
    have hb : b ≤ a := by simpa using h
    exact UInt64.toNat_sub_of_le a b hb

private theorem sub32_nat (a b : UInt64) : (sub32 a b).toNat = (a.toNat - b.toNat) % 4294967296 := by
  unfold sub32
  split
  · simp_all [UInt64.lt_iff_toNat_lt]; omega
  · next h =>
    have hb : b ≤ a := by simpa using h
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le a b hb]

private theorem low_nat (a b : UInt64) : (low a b).toNat = min a.toNat b.toNat := by
  unfold low
  split <;> simp_all [UInt64.lt_iff_toNat_lt] <;> omega

private theorem high_nat (a b : UInt64) : (high a b).toNat = max a.toNat b.toNat := by
  unfold high
  split <;> simp_all [UInt64.lt_iff_toNat_lt] <;> omega

private theorem signed_val (x : Int32) : x.toInt = if x.toUInt32.toNat < 2147483648 then
      (x.toUInt32.toNat : Int) else (x.toUInt32.toNat : Int) - 4294967296 := by
  simp only [Int32.toInt, BitVec.toInt_eq_toNat_cond, Int32.toBitVec, UInt32.toNat_toBitVec]
  change (if 2 * x.toUInt32.toNat < 4294967296 then (x.toUInt32.toNat : Int)
    else (x.toUInt32.toNat : Int) - 4294967296) = _
  split <;> split <;> omega

private theorem lift_val (x : Int32) : ((lift x).toNat : Int) = 12884901888 + x.toInt := by
  have hn := x.toUInt32.toNat_lt
  have hx := signed_val x
  unfold lift
  split <;> simp_all [UInt32.lt_iff_toNat_lt] <;> omega

private theorem position_val (pin : Bool) (base : UInt32) (origin sample : Int32) :
    ((position pin base origin sample).toNat : Int) =
      12884901888 + Translate.position pin base.toNat origin.toInt sample.toInt := by
  have ho := lift_val origin
  have hs := lift_val sample
  have ob := origin.le_toInt
  have ot := origin.toInt_lt
  have sb := sample.le_toInt
  have st := sample.toInt_lt
  have bn := base.toNat_lt
  unfold position Translate.position
  cases pin
  · simp only [Bool.false_eq_true, ite_false, sub_nat, UInt32.toNat_toUInt64, UInt64.reduceToNat]
    rw [add_nat _ _ (by omega)]
    omega
  · simpa using ho

private theorem fill_val (pin : Bool) (base top bottom : UInt32) (sample : Int32) :
    ((fillOrigin pin base top bottom sample).toNat : Int) =
      12884901888 + Translate.fillOrigin pin base.toNat sample.toInt top.toNat bottom.toNat := by
  have hs := lift_val sample
  have sb := sample.le_toInt
  have st := sample.toInt_lt
  have bn := base.toNat_lt
  have tn := top.toNat_lt
  have zn := bottom.toNat_lt
  have offset : ((if pin then 12884901888 + base.toUInt64 else lift sample).toNat : Int) =
      12884901888 + (if pin then (base.toNat : Int) else sample.toInt) := by
    cases pin
    · simpa using hs
    · simp only [ite_true]
      rw [add_nat _ _ (by simp; omega)]
      simp
  let off : UInt64 := if pin then 12884901888 + base.toUInt64 else lift sample
  have range : off.toNat < 17179869184 := by dsimp [off]; split <;> simp_all <;> omega
  change ((sub (12884901888 + top.toUInt64) 48 + (sub (off + bottom.toUInt64) top.toUInt64 % 48)).toNat : Int) = _
  have hp := add_nat (12884901888 : UInt64) top.toUInt64 (by simp; omega)
  have ho := add_nat off bottom.toUInt64 (by simp; omega)
  rw [add_nat _ _ (by simp only [sub_nat, UInt64.toNat_mod, hp, ho, UInt32.toNat_toUInt64, UInt64.reduceToNat]; omega)]
  simp only [sub_nat, UInt64.toNat_mod, hp, ho, UInt32.toNat_toUInt64, UInt64.reduceToNat]
  unfold Translate.fillOrigin
  dsimp [off] at *
  omega

private theorem crop_eq (which : UInt8) (p h top bottom : UInt64)
    (pb : p.toNat < 34359738368) (hb : h.toNat < 8589934592)
    (tb : top.toNat < 4294967296) (bb : bottom.toNat < 4294967296) :
    crop which p h top bottom =
      let r := Surface.crop ((p.toNat : Int) - 12884901888) h.toNat top.toNat bottom.toNat
      (if which == 0 then r.src0 else if which == 1 then r.src1
        else if which == 2 then r.dst0 else r.dst1).toUInt32 := by
  have ht := add_nat (12884901888 : UInt64) top (by simp; omega)
  have hb' := add_nat (12884901888 : UInt64) bottom (by simp; omega)
  let a := low h (sub (12884901888 + top) p)
  let z := high a (low h (sub (12884901888 + bottom) p))
  have ha : a.toNat = min h.toNat (12884901888 + top.toNat - p.toNat) := by
    simp [a, low_nat, sub_nat, ht]
  have hz : z.toNat = max a.toNat (min h.toNat (12884901888 + bottom.toNat - p.toNat)) := by
    simp only [z, high_nat, low_nat, sub_nat, hb', UInt64.reduceToNat]
  have ab : a.toNat ≤ h.toNat := by omega
  have zb : z.toNat ≤ h.toNat := by omega
  have pa := add_nat p a (by omega)
  have pz := add_nat p z (by omega)
  have xt : ((top.toNat : Int) - (p.toNat - 12884901888)).toNat =
      12884901888 + top.toNat - p.toNat := by omega
  have xb : ((bottom.toNat : Int) - (p.toNat - 12884901888)).toNat =
      12884901888 + bottom.toNat - p.toNat := by omega
  have da : ((p.toNat : Int) - 12884901888 + a.toNat).toNat =
      p.toNat + a.toNat - 12884901888 := by omega
  have dz : ((p.toNat : Int) - 12884901888 + z.toNat).toNat =
      p.toNat + z.toNat - 12884901888 := by omega
  change (if which == 0 then a.toUInt32 else if which == 1 then z.toUInt32
    else if which == 2 then sub32 (p + a) 12884901888 else sub32 (p + z) 12884901888) = _
  simp only [Surface.crop, xt, xb, ← ha, ← hz]
  split <;> (try split) <;> (try split) <;>
    apply UInt32.toNat.inj <;>
    simp_all [UInt64.toNat_toUInt32, sub32_nat] <;> omega

/-- The actual exported rectangle equals Translate.edge for every ABI input. -/
theorem edge_eq (fill : Bool) (which : UInt8) (pin : Bool) (base : UInt32)
    (origin : Int32) (height top bottom : UInt32) (sample : Int32) :
    edge fill which pin base origin height top bottom sample =
      Translate.edge fill which pin base origin height top bottom sample := by
  have hp := position_val pin base origin sample
  have hf := fill_val pin base top bottom sample
  have tn := top.toNat_lt
  have bn := bottom.toNat_lt
  have hn := height.toNat_lt
  have sn := sample.le_toInt
  have sx := sample.toInt_lt
  have on := origin.le_toInt
  have ox := origin.toInt_lt
  have ba := base.toNat_lt
  have pv : (position pin base origin sample).toNat < 34359738368 := by
    unfold Translate.position at hp; split at hp <;> omega
  have fv : (fillOrigin pin base top bottom sample).toNat < 34359738368 := by
    unfold Translate.fillOrigin at hf
    have hm := Int.emod_nonneg ((if pin then (base.toNat : Int) else sample.toInt) + bottom.toNat - top.toNat) (by decide : (48 : Int) ≠ 0)
    have hx := Int.emod_lt_of_pos ((if pin then (base.toNat : Int) else sample.toInt) + bottom.toNat - top.toNat) (by decide : (0 : Int) < 48)
    omega
  have hh : (sub bottom.toUInt64 top.toUInt64 + 48).toNat = bottom.toNat - top.toNat + 48 := by
    rw [add_nat _ _ (by simp [sub_nat]; omega)]
    simp [sub_nat]
  unfold edge Translate.edge
  cases fill
  · simp only [Bool.false_eq_true, ite_false]
    rw [crop_eq _ _ _ _ _ pv (by simp; omega) (by simpa using tn) (by simpa using bn)]
    simp only [UInt32.toNat_toUInt64, Translate.rect]
    rw [show ((position pin base origin sample).toNat : Int) - 12884901888 =
      Translate.position pin base.toNat origin.toInt sample.toInt by omega]
  · simp only [ite_true]
    rw [crop_eq _ _ _ _ _ fv (by omega) (by simpa using tn) (by simpa using bn)]
    simp only [hh, UInt32.toNat_toUInt64, Translate.fillRect]
    rw [show ((fillOrigin pin base top bottom sample).toNat : Int) - 12884901888 =
      Translate.fillOrigin pin base.toNat sample.toInt top.toNat bottom.toNat by omega]

/-- Signed displacement has the same wrapping ABI bits, without boxing. -/
theorem delta_eq (pin : Bool) (base : UInt32) (sample : Int32) :
    delta pin base sample = Translate.delta pin base sample := by
  cases pin
  · apply Int32.toBitVec.inj
    apply BitVec.eq_of_toNat_eq
    change (sample.toUInt32 - base).toNat = (BitVec.ofInt 32 (sample.toInt - base.toNat)).toNat
    simp only [UInt32.toNat_sub, BitVec.toNat_ofInt, Nat.reducePow]
    have hs := signed_val sample
    have hn := sample.toUInt32.toNat_lt
    have hb := base.toNat_lt
    change (4294967296 - base.toNat + sample.toUInt32.toNat) % 4294967296 =
      ((sample.toInt - base.toNat) % (4294967296 : Int)).toNat
    split at hs <;> omega
  · rfl

/-- The exported fill index equals the integer selector, even outside the viewport. -/
theorem fillRow_eq (pin : Bool) (base top bottom : UInt32) (sample : Int32) (y : UInt32) :
    fillRow pin base top bottom sample y = Translate.fillRow pin base top bottom sample y := by
  have hf := fill_val pin base top bottom sample
  have yn := y.toNat_lt
  have hy := add_nat (12884901888 : UInt64) y.toUInt64 (by simp; omega)
  apply UInt32.toNat.inj
  simp only [fillRow, Translate.fillRow, sub32_nat, hy,
    UInt32.toNat_toUInt64, UInt64.reduceToNat, UInt32.toNat_ofNat', Nat.reducePow]
  congr 1
  omega

private theorem int64_val (x : UInt64) (h : x.toNat < 9223372036854775808) :
    x.toInt64.toInt = x.toNat := by
  change x.toBitVec.toInt = x.toNat
  rw [BitVec.toInt_eq_toNat_of_lt (by change 2 * x.toNat < 18446744073709551616; omega)]
  rfl

/-- The exported painted-row selector equals the original Option-based one. -/
theorem pick_eq (pin : Bool) (base : UInt32) (origin : Int32) (height : UInt32)
    (sample : Int32) (y : UInt32) :
    pick pin base origin height sample y = Translate.pick pin base origin height sample y := by
  have hp := position_val pin base origin sample
  have yn := y.toNat_lt
  have hn := height.toNat_lt
  let p := position pin base origin sample
  let q : UInt64 := 12884901888 + y.toUInt64
  have hq : q.toNat = 12884901888 + y.toNat := by
    rw [add_nat _ _ (by simp; omega)]; simp
  apply Int64.toInt.inj
  rw [Translate.pick_source]
  change (if p ≤ q && q - p < height.toUInt64 then q - p else 18446744073709551615).toInt64.toInt = _
  by_cases le : p ≤ q
  · have hd := UInt64.toNat_sub_of_le q p le
    have le' := le
    rw [UInt64.le_iff_toNat_le] at le'
    by_cases lt : q - p < height.toUInt64
    · have lt' := lt
      rw [UInt64.lt_iff_toNat_lt] at lt'
      simp only [UInt32.toNat_toUInt64, hd] at lt'
      have hs : Translate.source pin base.toNat origin.toInt sample.toInt height.toNat y.toNat = some (q - p).toNat := by
        apply (Translate.source_iff ..).mpr
        dsimp [p] at *
        constructor <;> omega
      simp only [le, lt, decide_true, Bool.and_self, ite_true, hs]
      exact int64_val _ (by omega)
    · have lt' := lt
      rw [UInt64.lt_iff_toNat_lt] at lt'
      simp only [UInt32.toNat_toUInt64, hd] at lt'
      have hs : Translate.source pin base.toNat origin.toInt sample.toInt height.toNat y.toNat = none := by
        unfold Translate.source
        dsimp [p] at *
        split <;> simp_all <;> omega
      simp only [le, lt, decide_true, decide_false, Bool.true_and, hs]
      rfl
  · have le' := le
    rw [UInt64.le_iff_toNat_le] at le'
    have hs : Translate.source pin base.toNat origin.toInt sample.toInt height.toNat y.toNat = none := by
      unfold Translate.source
      dsimp [p] at *
      split <;> simp_all <;> omega
    simp only [le, decide_false, Bool.false_and, hs]
    rfl

end Slide
