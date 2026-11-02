import engine.renderer.DemandRank

/-! Synthetic message-component requests: two row owners share a query,
background work precedes a visible query, and unmount/remount rejects an
old callback. Every README theorem is instantiated with fully supplied
premises; separate computations check concrete results and failure cases. -/
namespace Vacuity.RendererDemand

private def rowA : Demand.Owner := [ByteArray.mk #[0x61]]
private def rowB : Demand.Owner := [ByteArray.mk #[0x62]]
def needs : List (Demand.Need Nat) :=
  [⟨rowA, 101, false⟩, ⟨rowB, 101, true⟩, ⟨rowB, 202, true⟩]
def mounted : Demand.Plan Nat := ({} : Demand.Plan Nat).reconcile needs

theorem ownership : mounted.held 101 = true ↔ ∃ n ∈ needs, n.key = 101 :=
  Demand.owned_iff {} needs 101
example : mounted.held 101 = true ∧ mounted.held 303 = false := by decide

theorem visiblePriority : (fun k : Nat => k == 202) 202 = true :=
  Demand.next_visible (fun k : Nat => k == 202) false [101, 202, 303] 202
    ⟨202, by decide, by decide⟩ (by decide)
example : Demand.next (fun k : Nat => k == 202) false [101, 202, 303] = some 202 := by decide
example : Demand.next (fun _ : Nat => false) false [101, 202, 303] = none := by decide

theorem fifo : (([303, 101, 202] : List Nat).filter ([101, 202, 404] : List Nat).contains).IsPrefix
    (Demand.reconcile [101, 202, 404] [303, 101, 202]) :=
  Demand.retained_prefix [101, 202, 404] [303, 101, 202]
example : Demand.reconcile [101, 202, 404] [303, 101, 202] = [101, 202, 404] := by decide

theorem retired : Demand.complete (mounted.reconcile []) ⟨101, 0⟩ "decoded photo" = none :=
  Demand.complete_retired _ _ _ (by decide)
example : Demand.complete mounted ⟨101, 0⟩ "decoded photo" = some "decoded photo" := by decide

theorem retained :
    (mounted.reconcile [⟨rowB, 101, true⟩]).ticket 101 = some ⟨101, 0⟩ :=
  Demand.retained_ticket mounted [⟨rowB, 101, true⟩] 101 ⟨101, 0⟩ (by decide) (by decide)

theorem beforeNext : mounted.BeforeNext :=
  Demand.reconcile_before_next {} needs Demand.empty_before_next

theorem remount : ((mounted.reconcile []).reconcile needs).current ⟨101, 0⟩ = false :=
  Demand.remount_rejects mounted [] needs 101 ⟨101, 0⟩ ⟨101, 2⟩
    beforeNext (by decide) (by decide) (by decide)
example : ((mounted.reconcile []).reconcile needs).ticket 101 = some ⟨101, 2⟩ := by decide
example : ¬ mounted.current ⟨101, 99⟩ = true := by decide

-- A user's act touched 202; 101 was queued, visible, in an earlier pass.
def actQueue : List Nat := Demand.reconcileFirst (· == 202) [202, 101] [101]
example : actQueue = [202, 101] := by decide
theorem actSorted : Demand.FirstSorted (· == 202) actQueue :=
  Demand.reconcileFirst_sorted (· == 202) [202, 101] [101]
theorem actFirst : ∃ x, (Demand.take (fun k : Nat => (k == 202) || true) true actQueue).1 = some x ∧ (x == 202) = true :=
  Demand.take_first (· == 202) (fun _ => true) true actQueue actSorted ⟨202, by decide, by decide⟩
theorem actRest : Demand.FirstSorted (· == 202) (Demand.take (fun k : Nat => (k == 202) || true) true actQueue).2 :=
  Demand.take_sorted (· == 202) (fun _ => true) true actQueue actSorted
theorem actMembers : 101 ∈ actQueue ↔ 101 ∈ Demand.reconcile [202, 101] [101] :=
  Demand.mem_reconcileFirst (· == 202) [202, 101] [101] 101
example : (Demand.take (fun k : Nat => (k == 202) || true) true (Demand.reconcile [202, 101] [101])).1 = some 101 := by decide

end Vacuity.RendererDemand
