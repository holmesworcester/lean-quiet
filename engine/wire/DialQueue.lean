/- Bounded FIFO admission of deferred dial addresses. The native runner calls
reserve while holding the same Slots mutex as its listener, so it cannot lose
a failed reservation or let a new retry overtake an older waiting address. -/
import engine.wire.Slots

namespace Engine.Sync.DialQueue

private theorem byteArrayBEq : LawfulBEq ByteArray where
  rfl := by intro a; change (a.data == a.data) = true; simp
  eq_of_beq := by intro a b h; change (a.data == b.data) = true at h; exact ByteArray.ext (by simpa using h)

attribute [local instance] byteArrayBEq

def enqueue (limit : Nat) (address : ByteArray) (waiting : List ByteArray) : List ByteArray :=
  if waiting.contains address then waiting
  else if waiting.length < limit then waiting ++ [address]
  else waiting

def reserve (cfg : RunConfig) : List String → List ByteArray → List ByteArray × List String
  | occupied, [] => ([], occupied)
  | occupied, address :: waiting =>
    if admit cfg occupied (peerHost address) then
      let (chosen, next) := reserve cfg (peerHost address :: occupied) waiting
      (address :: chosen, next)
    else reserve cfg occupied waiting

/-- New arrivals cannot increase the first position of an address already
waiting, even if new attempts keep arriving indefinitely. -/
theorem enqueue_pending (limit : Nat) (address target : ByteArray) (waiting : List ByteArray)
    (h : target ∈ waiting) :
    target ∈ enqueue limit address waiting ∧
      (enqueue limit address waiting).idxOf target ≤ waiting.idxOf target := by
  unfold enqueue
  split
  · exact ⟨h, Nat.le_refl _⟩
  · split
    · simp [List.mem_append, h, List.idxOf_append]
    · exact ⟨h, Nat.le_refl _⟩

theorem enqueue_bounded (limit : Nat) (address : ByteArray) (waiting : List ByteArray)
    (h : waiting.length ≤ limit) : (enqueue limit address waiting).length ≤ limit := by
  unfold enqueue
  split
  · exact h
  · split
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · exact h

/-- The queued head is admitted whenever its global and host quotas permit.
In particular, later retry frames cannot take that slot first. -/
theorem reserve_head (cfg : RunConfig) (occupied : List String)
    (address : ByteArray) (waiting : List ByteArray)
    (h : admit cfg occupied (peerHost address) = true) :
    address ∈ (reserve cfg occupied (address :: waiting)).1 := by
  simp [reserve, h]

theorem reserve_mem (cfg : RunConfig) (occupied : List String) (waiting : List ByteArray)
    {address : ByteArray} (h : address ∈ (reserve cfg occupied waiting).1) :
    address ∈ waiting := by
  induction waiting generalizing occupied with
  | nil => simp [reserve] at h
  | cons a rest ih =>
    by_cases ha : admit cfg occupied (peerHost a) = true
    · simp only [reserve, ha, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ h)
    · simp only [reserve, ha, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih _ h)

/-- The admission scan never reverses the order of selected destinations. -/
theorem reserve_order (cfg : RunConfig) (occupied : List String) (waiting : List ByteArray) :
    (reserve cfg occupied waiting).1.Sublist waiting := by
  induction waiting generalizing occupied with
  | nil => exact List.Sublist.refl []
  | cons a rest ih =>
    by_cases ha : admit cfg occupied (peerHost a) = true
    · simpa only [reserve, ha, ↓reduceIte] using
        List.Sublist.cons_cons a (ih (peerHost a :: occupied))
    · simpa only [reserve, ha, Bool.false_eq_true, ↓reduceIte] using
        List.Sublist.cons a (ih occupied)

/-- Atomic batch reservation preserves the native global socket bound. -/
theorem reserve_bounded (cfg : RunConfig) (occupied : List String) (waiting : List ByteArray)
    (h : occupied.length ≤ cfg.maxSocks) :
    (reserve cfg occupied waiting).2.length ≤ cfg.maxSocks := by
  induction waiting generalizing occupied with
  | nil => exact h
  | cons a rest ih =>
    by_cases ha : admit cfg occupied (peerHost a) = true
    · simpa only [reserve, ha, ↓reduceIte] using ih (peerHost a :: occupied) (admit_bounded cfg occupied _ ha).1
    · simpa only [reserve, ha, Bool.false_eq_true, ↓reduceIte] using ih occupied h

end Engine.Sync.DialQueue
