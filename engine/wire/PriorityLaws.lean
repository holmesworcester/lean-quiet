/- Bounded service of the exact 3:1 selector called by Loop.turn. Producers
may keep appending forever. Bounds count completed turns, not OS wall time. -/
import engine.wire.Priority
import engine.wire.LaneLaws

namespace Engine.Sync.Inbox.Priority

theorem advance_at_zero (slot : Slot) (h : slot.val = 0) : advance slot = first := by
  simp [advance, h]

theorem advance_positive (slot : Slot) (h : slot.val ≠ 0) :
    (advance slot).val + 1 = slot.val := by
  simp only [advance, h, dite_false]
  have := slot.isLt
  omega

def phaseAfter (slot : Slot) : Nat → Slot
  | 0 => slot
  | n + 1 => advance (phaseAfter slot n)

/-- Every phase returns after exactly four completed polls. -/
theorem phase_cycle (slot : Slot) : phaseAfter slot 4 = slot := by
  have all : ∀ s : Slot, phaseAfter s 4 = s := by decide
  exact all slot

/-- Every four consecutive turns prefer local work three times. This does
not count fallback network service in turns where no local work is ready. -/
theorem local_share (slot : Slot) :
    ((List.range 4).filter fun i => localFirst (phaseAfter slot i)).length = 3 := by
  have all : ∀ s : Slot, ((List.range 4).filter fun i => localFirst (phaseAfter s i)).length = 3 := by decide
  exact all slot

theorem step_write {W E : Type} (w : W) (ws : List W) (es : List E) (slot : Slot)
    (h : slot.val ≠ 0) :
    step ⟨w :: ws, es, slot⟩ = (some (.inl w), ⟨ws, es, advance slot⟩) := by
  simp [step, next, Inbox.next, localFirst, h, popW]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem step_event {W E : Type} (ws : List W) (e : E) (es : List E) (slot : Slot)
    (h : slot.val = 0) :
    step ⟨ws, e :: es, slot⟩ = (some (.inr e), ⟨ws, es, advance slot⟩) := by
  simp [step, next, Inbox.next, localFirst, h, popE]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem step_only_write {W E : Type} (w : W) (ws : List W) (slot : Slot) :
    step (⟨w :: ws, [], slot⟩ : State W E) = (some (.inl w), ⟨ws, [], advance slot⟩) := by
  by_cases h : slot.val = 0 <;> simp [step, next, Inbox.next, localFirst, h, popW, popE] <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem step_only_event {W E : Type} (e : E) (es : List E) (slot : Slot) :
    step (⟨[], e :: es, slot⟩ : State W E) = (some (.inr e), ⟨[], es, advance slot⟩) := by
  by_cases h : slot.val = 0 <;> simp [step, next, Inbox.next, localFirst, h, popW, popE] <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

inductive Waiting {W E : Type} : State W E → W ⊕ E → Nat → Prop
  | write (s : State W E) (pre post : List W) (w : W) (h : s.writes = pre ++ w :: post) :
      Waiting s (.inl w) (2 * pre.length + if s.slot.val = 0 then 2 else 1)
  | event (s : State W E) (pre post : List E) (e : E) (h : s.events = pre ++ e :: post) :
      Waiting s (.inr e) (4 * pre.length + s.slot.val + 1)

/-- Every completed poll serves the waiting entry or strictly reduces a
finite rank. Tail arrivals do not change the rank of existing work. -/
theorem waiting_step {W E : Type} {s : State W E} {x : W ⊕ E} {n : Nat}
    (h : Waiting s x n) (ws : List W) (es : List E) :
    (step s).1 = some x ∨ ∃ k < n, Waiting ((step s).2.append ws es) x k := by
  cases h with
  | write pre post w h =>
    rcases s with ⟨writes, events, slot⟩
    dsimp at h
    subst writes
    by_cases hz : slot.val = 0
    · cases events with
      | nil =>
        cases pre with
        | nil => exact Or.inl (by simpa only [List.nil_append] using (congrArg Prod.fst (step_only_write (E := E) w post slot)))
        | cons p pre =>
          rw [show (p :: pre) ++ w :: post = p :: (pre ++ w :: post) from rfl, step_only_write]
          right
          refine ⟨2 * pre.length + 1, by simp [hz]; omega, ?_⟩
          simpa [State.append, advance_at_zero slot hz, first, List.append_assoc] using
            Waiting.write (⟨(pre ++ w :: post) ++ ws, es, advance slot⟩ : State W E)
              pre (post ++ ws) w (by simp [List.append_assoc])
      | cons e events =>
        rw [step_event _ e events slot hz]
        right
        refine ⟨2 * pre.length + 1, by simp [hz], ?_⟩
        simpa [State.append, advance_at_zero slot hz, first, List.append_assoc] using
          Waiting.write (⟨(pre ++ w :: post) ++ ws, events ++ es, advance slot⟩ : State W E)
            pre (post ++ ws) w (by simp [List.append_assoc])
    · cases pre with
      | nil => exact Or.inl (by simpa only [List.nil_append] using (congrArg Prod.fst (step_write w post events slot hz)))
      | cons p pre =>
        rw [show (p :: pre) ++ w :: post = p :: (pre ++ w :: post) from rfl,
          step_write _ _ _ slot hz]
        right
        refine ⟨2 * pre.length + if (advance slot).val = 0 then 2 else 1,
          by simp only [List.length_cons, hz, ite_false]; split <;> omega, ?_⟩
        apply Waiting.write _ pre (post ++ ws) w
        simp [State.append, List.append_assoc]
  | event pre post e h =>
    rcases s with ⟨writes, events, slot⟩
    dsimp at h
    subst events
    by_cases hz : slot.val = 0
    · cases pre with
      | nil => exact Or.inl (by simpa only [List.nil_append] using (congrArg Prod.fst (step_event writes e post slot hz)))
      | cons p pre =>
        rw [show (p :: pre) ++ e :: post = p :: (pre ++ e :: post) from rfl,
          step_event _ _ _ slot hz]
        right
        refine ⟨4 * pre.length + (advance slot).val + 1,
          by simp [advance_at_zero slot hz, first, hz]; omega, ?_⟩
        apply Waiting.event _ pre (post ++ es) e
        simp [State.append, List.append_assoc]
    · cases writes with
      | nil =>
        cases pre with
        | nil => exact Or.inl (by simpa only [List.nil_append] using (congrArg Prod.fst (step_only_event (W := W) e post slot)))
        | cons p pre =>
          rw [show (p :: pre) ++ e :: post = p :: (pre ++ e :: post) from rfl, step_only_event]
          right
          refine ⟨4 * pre.length + (advance slot).val + 1, ?_, ?_⟩
          · have := (advance slot).isLt; simp only [List.length_cons]; omega
          · apply Waiting.event _ pre (post ++ es) e
            simp [State.append, List.append_assoc]
      | cons w writes =>
        rw [step_write _ _ _ slot hz]
        right
        refine ⟨4 * pre.length + (advance slot).val + 1, ?_, ?_⟩
        · have := advance_positive slot hz; dsimp only; omega
        · apply Waiting.event _ pre (post ++ es) e
          simp [State.append, List.append_assoc]

structure Run (W E : Type) where
  state : Nat → State W E
  writes : Nat → List W
  events : Nat → List E
  next : ∀ i, state (i + 1) = (step (state i)).2.append (writes i) (events i)

def Run.selected {W E : Type} (r : Run W E) (i : Nat) : Option (W ⊕ E) := (step (r.state i)).1

def states {W E : Type} (initial : State W E) (writes : Nat → List W) (events : Nat → List E) :
    Nat → State W E
  | 0 => initial
  | i + 1 => (step (states initial writes events i)).2.append (writes i) (events i)

def run {W E : Type} (initial : State W E) (writes : Nat → List W) (events : Nat → List E) : Run W E :=
  { state := states initial writes events, writes, events, next := fun _ => rfl }

theorem served {W E : Type} (r : Run W E) {n : Nat} :
    ∀ (i : Nat) (x : W ⊕ E), Waiting (r.state i) x n →
      ∃ j, i ≤ j ∧ j < i + n ∧ r.selected j = some x := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i x hw
    rcases waiting_step hw (r.writes i) (r.events i) with hs | ⟨k, hk, hw'⟩
    · have hn : 0 < n := by
        cases hw with
        | write => split <;> omega
        | event => omega
      exact ⟨i, Nat.le_refl _, by omega, hs⟩
    · rw [← r.next i] at hw'
      obtain ⟨j, hj, hb, hs⟩ := ih k hk (i + 1) x hw'
      exact ⟨j, by omega, by omega, hs⟩

/-- A queued local head waits at most one reserved network turn. -/
theorem write_within {W E : Type} (r : Run W E) (i : Nat) (pre post : List W) (w : W)
    (h : (r.state i).writes = pre ++ w :: post) :
    ∃ j, i ≤ j ∧ j < i + 2 * (pre.length + 1) ∧ r.selected j = some (.inl w) := by
  obtain ⟨j, hj, hb, hs⟩ := served r i (.inl w) (Waiting.write _ pre post w h)
  refine ⟨j, hj, ?_, hs⟩
  split at hb <;> omega

/-- One guaranteed event slot in four, even under sustained local writes. -/
theorem event_within {W E : Type} (r : Run W E) (i : Nat) (pre post : List E) (e : E)
    (h : (r.state i).events = pre ++ e :: post) :
    ∃ j, i ≤ j ∧ j < i + 4 * (pre.length + 1) ∧ r.selected j = some (.inr e) := by
  obtain ⟨j, hj, hb, hs⟩ := served r i (.inr e) (Waiting.event _ pre post e h)
  have := (r.state i).slot.isLt
  exact ⟨j, hj, by omega, hs⟩

end Engine.Sync.Inbox.Priority
