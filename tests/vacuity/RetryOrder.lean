/- Nonempty infinite continuing-arrival witness for the actual executable
retry-admission core. This is not a whole Runner or delivery certificate. -/
import engine.wire.RetryOrderLaws
import engine.core.WindowIndex

namespace Vacuity.RetryOrder
open Engine.Sync.RetryOrder

def live (n : Nat) : List Nat := [0, 1, 2, n+3]
def address (_ : Nat) : Option Nat := some 0
def candidate (_ : Nat) : Bool := true

def queue : Nat → List Nat
  | 0 => [0, 1, 2]
  | n+1 => reconcile (live n) (offered (scan address candidate [] (queue n)).1 (queue n))

def run : Run Nat Nat := {
  queue, address := fun _ => address, candidate := fun _ => candidate,
  claimed := fun _ => [], live, next := fun _ => rfl }

theorem live_unique (n : Nat) : (live n).Nodup := by
  simp [live]

theorem unique (n : Nat) : (run.queue n).Nodup :=
  run.nodup (by decide +kernel) live_unique n

theorem continuing_arrival (n : Nat) : n+3 ∈ run.queue (n+1) := by
  rw [run.next]
  exact (reconcile_members _ _ _).mpr (by simp [run, live])

theorem always_live (n : Nat) : 2 ∈ run.queue n := by
  cases n with
  | zero => decide +kernel
  | succ n => rw [run.next]; exact (reconcile_members _ _ _).mpr (by simp [run, live])

theorem nonempty (n : Nat) : run.queue n ≠ [] := by
  intro empty
  have := always_live n
  simp [empty] at this

theorem opportunities (start n : Nat) : run.opportunities 2 start n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Run.opportunities, ih]
    rfl

theorem target_served : ∃ j, j < 3 ∧ 2 ∈ run.sent j := by
  have reached := offered_or_retired run unique 0 2 (by decide +kernel) 3 (by decide +kernel)
  obtain ⟨j, _, upper, served | retired⟩ := reached
  · exact ⟨j, by omega, served⟩
  · exact False.elim (retired (by simp [run, live]))

theorem first_three : [run.sent 0, run.sent 1, run.sent 2] = [[0], [1], [2]] := by decide +kernel

theorem infinitely_many_opportunities (start bound : Nat) :
    ∃ n, bound < run.opportunities 2 start n := ⟨bound+1, by rw [opportunities]; omega⟩

/- The running session/address representation also instantiates the law.
Its BEq law is the repository's proved ByteArray theorem, not an axiom. -/
attribute [local instance] Engine.lawfulBEqByteArray

def actualIds : List Engine.Id := ["Alice session".toUTF8, "Bob session".toUTF8, "Carol session".toUTF8]
def actualAddress (_ : Engine.Id) : Option ByteArray := some "shared socket".toUTF8

def actualQueue : Nat → List Engine.Id
  | 0 => actualIds
  | n+1 => reconcile actualIds (offered (scan actualAddress (fun _ => true) [] (actualQueue n)).1 (actualQueue n))

def actualRun : Run Engine.Id ByteArray := {
  queue := actualQueue, address := fun _ => actualAddress, candidate := fun _ _ => true,
  claimed := fun _ => [], live := fun _ => actualIds, next := fun _ => rfl }

theorem actual_unique (n : Nat) : (actualRun.queue n).Nodup :=
  actualRun.nodup (by decide +kernel) (fun _ => by change actualIds.Nodup; decide +kernel) n

theorem actual_id_service : ∃ j, j < 3 ∧ "Carol session".toUTF8 ∈ actualRun.sent j := by
  have reached := offered_or_retired actualRun actual_unique 0 "Carol session".toUTF8
    (by decide +kernel) 3 (by decide +kernel)
  obtain ⟨j, _, upper, served | retired⟩ := reached
  · exact ⟨j, by omega, served⟩
  · exact False.elim (retired (by change "Carol session".toUTF8 ∈ actualIds; decide +kernel))

#print axioms target_served
#print axioms actual_id_service

end Vacuity.RetryOrder
