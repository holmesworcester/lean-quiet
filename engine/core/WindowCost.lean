/-
What matching a filing costs (law 3), in the shared cost model
(engine/core/Cost.lean): the code that runs (`Subs.find`, `Subs.notifyM`),
run in `CostT`.

A filing under key k at position p costs a hash of k (k's bytes and one
probe: the hash map assumption, as the SQLite one is SQLite's file
format), then a binary search of k's windows' bounds, ⌊log₂ (2·S_k)⌋ + 2
comparisons of at most p's bytes each (`find_costs`), S_k being the
windows on k. Nothing else: no read, no list, no seek. A batch then costs
that per net filing plus one step per window found (`notify_cost`): the
O(log S + matches) per filing that exact notices need, whatever the
number of rows N.
-/
import engine.core.WindowIndex

namespace Engine

/-- The steps of a binary search over n positions: ⌊log₂ n⌋ + 1, and
none over none. -/
def searchSteps (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

theorem searchSteps_half {n n' : Nat} (hn : 0 < n) (h : n' ≤ n / 2) : 1 + searchSteps n' ≤ searchSteps n := by
  unfold searchSteps
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0]
  by_cases h0 : n' = 0
  · rw [if_pos h0]; omega
  · rw [if_neg h0]
    have : Nat.log2 n' + 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by
      have := Nat.log2_self_le h0
      rw [Nat.pow_succ]; omega)
    omega

theorem searchSteps_mono {a b : Nat} (h : a ≤ b) : searchSteps a ≤ searchSteps b := by
  unfold searchSteps
  by_cases ha : a = 0
  · rw [if_pos ha]; exact Nat.zero_le _
  · rw [if_neg ha, if_neg (by omega)]
    have : Nat.log2 a ≤ Nat.log2 b := (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le ha) h)
    omega

theorem work_le {a b : Nat} (h : a ≤ b) : ({ work := a } : Meter) ≤ { work := b } :=
  Meter.le_iff.2 ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, h, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem work_add (a b : Nat) : ({ work := a } : Meter) + { work := b } = { work := a + b } := by
  ext <;> simp

/-! ## The search, counted -/

section
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **A binary search over n bounds costs ⌊log₂ n⌋ + 1 comparisons.** -/
theorem rank_costs (b : Array Pos) (p : Pos) : ∀ n lo hi, hi - lo = n →
    Costs { work := searchSteps n * posWork p } (rankM (m := CostT m) b p lo hi) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn
  rw [rankM]
  by_cases h : lo < hi
  · rw [dif_pos h]
    have br : ∀ lo' hi', hi' - lo' ≤ n / 2 →
        Costs { work := searchSteps (n / 2) * posWork p } (rankM (m := CostT m) b p lo' hi') := by
      intro lo' hi' hle
      exact (ih (hi' - lo') (by omega) lo' hi' rfl).mono
        (work_le (Nat.mul_le_mul_right _ (searchSteps_mono hle)))
    refine costs_bind_le (costs_tick _)
      (fun _ => costs_ite (fun _ => br _ _ (by omega)) (fun _ => br _ _ (by omega))) ?_
    rw [work_add]
    apply work_le
    have := Nat.mul_le_mul_right (posWork p) (searchSteps_half (n := n) (n' := n / 2) (by omega) (Nat.le_refl _))
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  · rw [dif_neg h]
    exact (costs_pure lo).mono (by meter_le)

theorem costs_tick_pure {α : Type} (c : Meter) (a : α) : Costs c (do tick c; pure a : CostT m α) := by
  have := costs_bind (costs_tick (m := m) c) (fun _ => costs_pure (m := m) a)
  rwa [Meter.add_zero] at this

/-- A key's slots: a search, and one more comparison. -/
theorem slots_find_costs {S : Type} (sl : Slots S) (p : Pos) :
    Costs { work := (searchSteps sl.bounds.size + 1) * posWork p } (sl.find (m := CostT m) p) := by
  unfold Slots.find
  refine costs_bind_le (rank_costs sl.bounds p _ 0 sl.bounds.size rfl)
    (fun _ => costs_tick_pure { work := posWork p } _) ?_
  rw [Nat.sub_zero, work_add]
  apply work_le
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.le_refl _

end

/-! ## Bounds per window -/

theorem length_dedupSorted_le : ∀ (l : List Pos), (dedupSorted l).length ≤ l.length
  | [] => Nat.le_refl _
  | [_] => Nat.le_refl _
  | a :: b :: t => by
    unfold dedupSorted
    have := length_dedupSorted_le (b :: t)
    split
    · simp only [List.length_cons] at *; omega
    · simp only [List.length_cons] at *; omega

theorem length_endsOf_le {S : Type} (ws : Array (S × Win)) : (endsOf ws).length ≤ 2 * ws.size := by
  unfold endsOf
  rw [← Array.length_toList]
  generalize ws.toList = l
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨x, w⟩ := a
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_map]
    have : w.lo.toList.length + w.hi.toList.length ≤ 2 := by
      cases w.lo <;> cases w.hi <;> simp
    omega

/-- A key's windows name at most two bounds each. -/
theorem size_boundsOf_le {S : Type} (ws : Array (S × Win)) : (boundsOf ws).size ≤ 2 * ws.size := by
  unfold boundsOf
  rw [List.size_toArray]
  exact Nat.le_trans (length_dedupSorted_le _) (by rw [List.length_mergeSort]; exact length_endsOf_le ws)

/-! ## Law 3 -/

section
variable {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}

/-- **Matching one filing costs O(log S_k)**: a hash of its key, and
⌊log₂ (2·S_k)⌋ + 2 comparisons of at most its position's bytes, S_k being
its key's windows; no store read, list, write or seek, whatever the rows. -/
theorem find_costs {I : Subs S} (hI : I.WF) (k : ByteArray) (p : Pos) :
    Costs { work := k.size + 1 + (searchSteps (2 * (I.at_ k).size) + 1) * posWork p }
      (I.find (m := CostT m) k p) := by
  unfold Subs.find
  have hm : Costs { work := (searchSteps (2 * (I.at_ k).size) + 1) * posWork p }
      (match I.keys[k]? with | none => pure #[] | some (_, sl) => sl.find (m := CostT m) p) := by
    split
    · exact (costs_pure _).mono (by meter_le)
    · rename_i ws sl he
      obtain ⟨hsl, _⟩ := hI k (ws, sl) he
      simp only at hsl
      have hat : I.at_ k = ws := by simp [Subs.at_eq, he]
      rw [hat]
      refine (slots_find_costs sl p).mono (work_le (Nat.mul_le_mul_right _ ?_))
      apply Nat.add_le_add_right
      apply searchSteps_mono
      rw [hsl, build_bounds]
      exact size_boundsOf_le ws
  exact costs_bind_le (costs_tick _) (fun _ => hm) (by rw [work_add]; exact work_le (Nat.le_refl _))

end

/-! ## A batch, counted -/

section
variable {S : Type}

theorem cost_le_of_costs {α : Type} {B : Meter} {x : Counted α} (h : Costs B x) :
    (Counted.cost x).work ≤ B.work := by
  obtain ⟨y, hy⟩ := h Meter.work
  show (Id.run x.run).2.work ≤ B.work
  rw [← hy]
  exact (Id.run y).2

theorem val_rankM (b : Array Pos) (p : Pos) : ∀ n lo hi, hi - lo = n →
    Counted.val (rankM (m := Counted) b p lo hi) = Id.run (rankM (m := _root_.Id) b p lo hi) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn
  rw [rankM_id]
  conv => lhs; rw [rankM]
  by_cases h : lo < hi
  · rw [dif_pos h, if_pos h, Counted.val_bind]
    split
    · exact ih _ (by omega) _ _ rfl
    · exact ih _ (by omega) _ _ rfl
  · rw [dif_neg h, if_neg h]; rfl

theorem val_find (I : Subs S) (k : ByteArray) (p : Pos) :
    Counted.val (I.find (m := Counted) k p) = Id.run (I.find (m := _root_.Id) k p) := by
  unfold Subs.find Slots.find
  simp only [Counted.val_bind, Counted.val_tick]
  split
  · rfl
  · simp only [Counted.val_bind, Counted.val_tick, Counted.val_pure]
    rw [val_rankM _ _ _ 0 _ rfl]
    rfl

/-- **A batch costs its filings' searches and one step per window
found.** -/
theorem notify_cost {I : Subs S} (hI : I.WF) : ∀ (J : List (ByteArray × Pos)),
    (Counted.cost (I.notifyM (m := Counted) J)).work ≤
      (J.map fun e => e.1.size + 1 + (searchSteps (2 * (I.at_ e.1).size) + 1) * posWork e.2).sum +
        (Id.run (I.notifyM (m := _root_.Id) J)).size
  | [] => by simp [Subs.notifyM]
  | (k, p) :: rest => by
    have ih := notify_cost hI rest
    have hf := cost_le_of_costs (find_costs (m := _root_.Id) hI k p)
    simp only [Subs.notifyM, Counted.cost_bind, Counted.val_bind, Counted.cost_tick, Counted.val_tick,
      Counted.cost_pure, Meter.work_add, Meter.work_zero, List.map_cons, List.sum_cons]
    rw [val_find]
    show _ ≤ _ + (Id.run (I.find k p) ++ Id.run (I.notifyM rest)).size
    rw [Array.size_append]
    simp only at hf ⊢
    omega

end

end Engine
