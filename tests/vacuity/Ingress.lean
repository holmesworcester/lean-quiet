/- Nonempty infinite executions of the exact executable selectors.
These witnesses certify selector premises, not native scheduling/IO refinement. -/
import engine.wire.IngressChurnLaws

namespace Vacuity.Ingress
open Engine.Sync.Ingress

theorem peerDeadline :
    ∃ j, 0 ≤ j ∧ j < 3 ∧ flooded.selected j = some (⟨2, by decide⟩, 2) :=
  source_within flooded 0 ⟨2, by decide⟩ 2 rfl

def writes (i : Nat) : List Nat := [i + 2]
def events (i : Nat) : List (Fin 3 × Nat) :=
  [(⟨0, by decide⟩, 100 + i), (⟨1, by decide⟩, 200 + i), (⟨2, by decide⟩, 300 + i)]
def combinedStates : Nat → Prioritized.State Nat Nat 2
  | 0 => { writes := [0, 1], inbox := { slots := #v[some 10, some 11, some 12] } }
  | i + 1 => ((Prioritized.step (combinedStates i)).2).arrivals (writes i) (events i)
def combined : Prioritized.Run Nat Nat 2 :=
  { state := combinedStates, writes, events, next := fun _ => rfl }

theorem combinedPeerDeadline :
    ∃ j, 0 ≤ j ∧ j < 12 ∧ combined.selected j = some (.inr (⟨1, by decide⟩, 11)) :=
  Prioritized.source_within combined 0 ⟨1, by decide⟩ 11 rfl

theorem combinedWriteDeadline :
    ∃ j, 0 ≤ j ∧ j < 4 ∧ combined.selected j = some (.inl 1) :=
  Prioritized.write_within combined 0 [0] [] 1 rfl

theorem churnPeerDeadline :
    ∃ j, 0 ≤ j ∧ j < 12 ∧
      Prioritized.churnFlood.selected j = some (.inr (⟨1, by decide⟩, 11)) :=
  Prioritized.churnFlood_source

theorem churnWriteDeadline :
    ∃ j, 0 ≤ j ∧ j < 2 ∧ Prioritized.churnFlood.selected j = some (.inl 0) :=
  Prioritized.churnFlood_write

/-- Both flows stay populated; the target exists before the checked steps. -/
theorem exactPrefix :
    combined.selected 0 = some (.inl 0) ∧
    combined.selected 1 = some (.inl 1) ∧
    combined.selected 3 = some (.inr (⟨0, by decide⟩, 10)) ∧
    combined.selected 7 = some (.inr (⟨1, by decide⟩, 11)) := by decide

def zero : Fin 3 := ⟨0, by decide⟩
def one : Fin 3 := ⟨1, by decide⟩
def two : Fin 3 := ⟨2, by decide⟩
def inbox : State Nat 2 := { slots := #v[some 10, some 11, some 12] }
def first : Prioritized.State Nat Nat 2 := combined.state 0

theorem distanceBound : distance zero two < 3 := distance_lt zero two
theorem distanceAdvance : distance (advance zero) two + 1 = distance zero two :=
  advance_distance zero two (by decide)

theorem scanReady : ∃ source selected next,
    scan inbox.slots 3 zero = (some (source, selected), next) ∧
    inbox.slots[source.val] = some selected ∧
    (source = two ∨ distance next two < distance zero two) :=
  scan_ready inbox.slots two 12 rfl 3 zero (by decide)

theorem pollProgress : inbox.poll.1 = some (two, 12) ∨
    (inbox.poll.2.slots[two.val] = some 12 ∧
      distance inbox.poll.2.cursor two < distance inbox.cursor two) :=
  poll_progress inbox two 12 rfl

theorem arrivalPreserves : (inbox.arrivals (events 0)).slots[one.val] = some 11 ∧
    (inbox.arrivals (events 0)).cursor = inbox.cursor :=
  arrivals_preserve inbox (events 0) one 11 rfl

theorem cancelPreserves : (inbox.cancelAll [two]).slots[one.val] = inbox.slots[one.val] ∧
    (inbox.cancelAll [two]).cursor = inbox.cursor :=
  cancelAll_preserves inbox [two] one (by decide)

theorem changesPreserve : (first.changes [2] [two] (events 0)).inbox.slots[one.val] = some 11 ∧
    Prioritized.rank (first.changes [2] [two] (events 0)) one = Prioritized.rank first one :=
  Prioritized.changes_preserve first [2] [two] (events 0) one 11 (by decide) rfl

theorem localBranch : (Prioritized.step first).1 = some (.inl 0) :=
  congrArg Prod.fst (Prioritized.step_write 0 [1] inbox Engine.Sync.Inbox.Priority.first (by decide))

def networkPhase : Engine.Sync.Inbox.Priority.Slot := ⟨0, by decide⟩

theorem networkBranch :
    (Prioritized.step ({ writes := [0, 1], inbox, phase := networkPhase } : Prioritized.State Nat Nat 2)).1 =
      some (.inr (zero, 10)) :=
  congrArg Prod.fst (Prioritized.step_event [0, 1] inbox networkPhase zero 10 rfl rfl)

theorem onlyNetworkBranch :
    (Prioritized.step ({ writes := [], inbox } : Prioritized.State Nat Nat 2)).1 = some (.inr (zero, 10)) :=
  congrArg Prod.fst (Prioritized.step_only_event inbox Engine.Sync.Inbox.Priority.first zero 10 rfl)

theorem emptyNetworkBranch :
    (Prioritized.step ({ writes := [0, 1], inbox := {}, phase := networkPhase } : Prioritized.State Nat Nat 2)).1 =
      some (.inl 0) :=
  congrArg Prod.fst (Prioritized.step_empty_event 0 [1] ({} : State Nat 2) networkPhase rfl rfl)

theorem churnPrefix : Prioritized.churnFlood.selected 0 = some (.inl 0) ∧
    Prioritized.churnFlood.selected 7 = some (.inr (one, 11)) := Prioritized.churnFlood_exact

theorem networkPrefix :
    ((List.range 9).map fun i => flooded.selected i |>.map (·.1.val)) =
      [some 0, some 1, some 2, some 0, some 1, some 2, some 0, some 1, some 2] := flooded_prefix

end Vacuity.Ingress
