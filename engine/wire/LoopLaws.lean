/- The dispatch equations and scheduler-state invariants of the turn the
native runner calls. Backend progress and storage/transport semantics are
separate obligations, not conclusions of these equations. -/
import engine.wire.Loop

namespace Engine.Sync

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] [Turn F m]
  (x : Sync F m) (n : Node) (now : Nat)

@[simp] theorem Node.step_write (ops : List Op) :
    n.step x (.write ops) now = n.onWrite x ops now := rfl

@[simp] theorem Node.step_frame (addr bytes : ByteArray) :
    n.step x (.frame addr bytes) now = n.onFrame x addr bytes now := rfl

@[simp] theorem Node.step_tick : n.step x .tick now = n.onTick x now := rfl

@[simp] theorem Node.step_close (addr : ByteArray) :
    n.step x (.close addr) now = n.onClose x addr now := rfl

end

namespace Loop

private theorem run_bind {μ α β : Type} (p : StateM μ α) (k : α → StateM μ β) (s : μ) :
    (p >>= k).run s = (k (p.run s).1).run (p.run s).2 := rfl

private theorem run_map {μ α β : Type} (f : α → β) (p : StateM μ α) (s : μ) :
    (f <$> p).run s = (f (p.run s).1, (p.run s).2) := rfl

private theorem run_pure {μ α : Type} (a : α) (s : μ) :
    (pure a : StateM μ α).run s = (a, s) := rfl

/-- Every return from dispatch preserves the observed input and the inbox
phase. Arbitrary backend callbacks can change their own state, not the
scheduler's state or the recorded input. -/
theorem dispatch_records {σ W E μ : Type} (backend : Backend (StateM μ) σ W E)
    (period : Nat) (state : State σ) (observed : Observation W E) (memory : μ) :
    let result := ((dispatch backend period state observed).run memory).1
    result.observed = observed ∧ result.state.slot = state.slot := by
  cases hs : observed.selected with
  | none =>
    simp only [dispatch, hs, run_bind, run_map, run_pure]
    split <;> simp_all [run_bind, run_map, run_pure] <;> exact ⟨rfl, rfl⟩
  | some input =>
    cases input with
    | inl w =>
      simp only [dispatch, hs, run_bind, run_map, run_pure]
      split <;> simp_all [run_bind, run_map, run_pure] <;> exact ⟨rfl, rfl⟩
    | inr e =>
      simp only [dispatch, hs, run_bind, run_map, run_pure]
      split <;> simp_all [run_bind, run_map, run_pure] <;>
        first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

/-- Every completed non-stopping dispatch uses precisely the production
timer decision, even when its primary input was a write or network event. -/
theorem dispatch_timer {σ W E μ : Type} (backend : Backend (StateM μ) σ W E)
    (period : Nat) (state : State σ) (observed : Observation W E) (memory : μ) :
    let result := ((dispatch backend period state observed).run memory).1
    result.stopped = false →
      (result.ticked, result.state.lastTick) = Tick.next period state.lastTick observed.now := by
  cases hs : observed.selected with
  | none =>
    simp only [dispatch, hs, run_bind, run_map, run_pure]
    split <;> simp_all [run_bind, run_map, run_pure] <;>
      exact fun _ => Prod.ext (by simp_all <;> rfl) rfl
  | some input =>
    cases input with
    | inl w =>
      simp only [dispatch, hs, run_bind, run_map, run_pure]
      split <;> simp_all [run_bind, run_map, run_pure] <;>
        exact fun _ => Prod.ext (by simp_all <;> rfl) rfl
    | inr e =>
      simp only [dispatch, hs, run_bind, run_map, run_pure]
      split <;> simp_all [run_bind, run_map, run_pure] <;>
        first
        | exact fun h => Bool.noConfusion h
        | split <;> exact fun _ => Prod.ext (by simp_all <;> rfl) rfl

private theorem inbox_phase {W E μ : Type} (slot : Inbox.Priority.Slot)
    (writes : StateM μ (Option W)) (events : StateM μ (Option E)) (memory : μ) :
    ((Inbox.Priority.next slot writes events).run memory).1.2 = Inbox.Priority.advance slot := rfl

/-- The actual turn, including its poll, advances its bounded phase once and records
the time sampled before polling. This is a property of completed calls; it
does not assume that a blocked native callback completes. -/
theorem turn_records {σ W E μ : Type} (backend : Backend (StateM μ) σ W E)
    (period : Nat) (state : State σ) (memory : μ) :
    let result := ((turn backend period state).run memory).1
    result.state.slot = Inbox.Priority.advance state.slot ∧
      result.observed.now = (backend.clock.run memory).1 := by
  let sampled := backend.clock.run memory
  let polled := (Inbox.Priority.next state.slot backend.writes backend.events).run sampled.2
  have h := dispatch_records backend period { state with slot := polled.1.2 }
    { now := sampled.1, selected := polled.1.1 } polled.2
  exact ⟨h.2.trans (inbox_phase state.slot backend.writes backend.events sampled.2),
    congrArg Observation.now h.1⟩

/-- The timer trace of actual turns is the timer trace used in the cofinal
tick theorem, with no caller-supplied decision replacing `Tick.next`. -/
theorem turn_timer {σ W E μ : Type} (backend : Backend (StateM μ) σ W E)
    (period : Nat) (state : State σ) (memory : μ) :
    let result := ((turn backend period state).run memory).1
    result.stopped = false →
      (result.ticked, result.state.lastTick) = Tick.next period state.lastTick result.observed.now := by
  let sampled := backend.clock.run memory
  let polled := (Inbox.Priority.next state.slot backend.writes backend.events).run sampled.2
  have h := dispatch_timer backend period { state with slot := polled.1.2 }
    { now := sampled.1, selected := polled.1.1 } polled.2
  have recorded := dispatch_records backend period { state with slot := polled.1.2 }
    { now := sampled.1, selected := polled.1.1 } polled.2
  dsimp only
  intro running
  exact (h running).trans (congrArg (Tick.next period state.lastTick)
    (congrArg Observation.now recorded.1).symm)

end Loop
end Engine.Sync
