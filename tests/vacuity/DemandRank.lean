import engine.renderer.DemandRank

namespace Vacuity.DemandRank
open Demand

def queue : Nat → List Nat
  | 0 => [0, 1, 2, 3]
  | 1 => [1, 3, 4, 5]
  | n + 2 => [n + 3, n + 4, n + 5, n + 6]

def visible (n key : Nat) : Bool := if n == 0 then key != 1 && key != 2 else true

def keep (n key : Nat) : Bool := if n == 0 then key != 2 else true

def added : Nat → List Nat
  | 0 => [4, 5]
  | n + 1 => [n + 6]

def run : SelectionRun Nat where
  queue
  visible
  background := fun _ => true
  keep
  added
  next := by
    intro n
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n => simp [queue, visible, keep, added, take, takeBy, next, List.find?, Nat.add_assoc]

theorem nonempty (n : Nat) : run.queue n ≠ [] := by
  cases n with
  | zero => decide
  | succ n => cases n <;> simp [run, queue]

theorem continuing_arrivals (n : Nat) : run.added n ≠ [] := by
  cases n <;> simp [run, added]

theorem distinct_arrivals (n : Nat) : n + 6 ∈ run.added (n + 1) := by simp [run, added]

theorem changed_priority : run.visible 0 1 = false ∧ run.visible 1 1 = true := by decide

theorem retired_predecessor : run.keep 0 2 = false := by decide

theorem initial_rank : (run.queue 0).idxOf 3 = 3 := by decide

theorem target_visible (n : Nat) : run.visible n 3 = true := by
  cases n <;> simp [run, visible]

theorem target_retained (n : Nat) : run.keep n 3 = true := by
  cases n <;> simp [run, keep]

theorem target_bound : ∃ j, 0 ≤ j ∧ j < 0 + 3 + 1 ∧
    ((take (run.visible j) (run.background j) (run.queue j)).1 = some 3 ∨ run.keep j 3 = false) :=
  selected_or_retired run 3 0 3 initial_rank (by decide) (fun n _ _ _ => target_visible n)

theorem selected_bound : ∃ j, 0 ≤ j ∧ j < 0 + (run.queue 0).idxOf 3 + 1 ∧
    (take (run.visible j) (run.background j) (run.queue j)).1 = some 3 :=
  selected_within run 0 3 (by decide) (fun n _ _ _ => target_visible n) (fun n _ _ => target_retained n)

theorem mapped_choice :
    next (visible 0) true ([((0 : Nat), "A"), (3, "T")].map Prod.fst) =
    (next (fun v => visible 0 v.1) true [(0, "A"), (3, "T")]).map Prod.fst :=
  next_map Prod.fst (visible 0) true _

theorem mapped_take :
    ((takeBy Prod.fst (visible 0) true [((0 : Nat), "A"), (3, "T")]).1.map Prod.fst,
     (takeBy Prod.fst (visible 0) true [(0, "A"), (3, "T")]).2.map Prod.fst) =
    take (visible 0) true ([((0 : Nat), "A"), (3, "T")].map Prod.fst) :=
  takeBy_map Prod.fst (visible 0) true _

theorem filter_preserves_rank :
    ((queue 0).filter (keep 0)).idxOf 3 ≤ (queue 0).idxOf 3 :=
  filter_rank (keep 0) (queue 0) 3 (by decide) (by decide)

theorem one_selection :
    (take (visible 0) true (queue 0)).1 = some 3 ∨
      3 ∈ (take (visible 0) true (queue 0)).2 ∧
      (take (visible 0) true (queue 0)).2.idxOf 3 < (queue 0).idxOf 3 :=
  take_progress (visible 0) true (queue 0) 3 (by decide) (by decide)

theorem changing_selection :
    (take (visible 0) true (queue 0)).1 = some 3 ∨
      3 ∈ (take (visible 0) true (queue 0)).2.filter (keep 0) ++ added 0 ∧
      ((take (visible 0) true (queue 0)).2.filter (keep 0) ++ added 0).idxOf 3 < (queue 0).idxOf 3 :=
  take_changes (visible 0) true (queue 0) (added 0) (keep 0) 3 (by decide) (by decide) (by decide)

theorem actual_selections : (take (run.visible 0) (run.background 0) (run.queue 0)).1 = some 0 ∧ (take (run.visible 1) (run.background 1) (run.queue 1)).1 = some 1 ∧
    (take (run.visible 2) (run.background 2) (run.queue 2)).1 = some 3 := by decide

#print axioms Demand.next_map
#print axioms Demand.takeBy_map
#print axioms Demand.filter_rank
#print axioms Demand.take_progress
#print axioms Demand.take_changes
#print axioms Demand.selected_within
#print axioms Demand.selected_or_retired
#print axioms mapped_choice
#print axioms mapped_take
#print axioms filter_preserves_rank
#print axioms one_selection
#print axioms changing_selection
#print axioms selected_bound
#print axioms target_bound
#print axioms actual_selections
end Vacuity.DemandRank
