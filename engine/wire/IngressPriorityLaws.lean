import engine.wire.IngressLaws
import engine.wire.PriorityLaws

namespace Engine.Sync.Ingress.Prioritized

structure State (W E : Type) (n : Nat) where
  writes : List W
  inbox : Ingress.State E n
  phase : Inbox.Priority.Slot := Inbox.Priority.first

def popWrite {W E : Type} {n : Nat} : StateM (List W × Ingress.State E n) (Option W) :=
  modifyGet fun (writes, inbox) => (writes.head?, (writes.tail, inbox))

def popEvent {W E : Type} {n : Nat} :
    StateM (List W × Ingress.State E n) (Option (Fin (n + 1) × E)) :=
  modifyGet fun (writes, inbox) =>
    let (selected, next) := inbox.poll
    (selected, (writes, next))

/-- Interpret the actual nested production selectors, without replacing
either the 3:1 local policy or the rotating peer mailbox poll. -/
def step {W E : Type} {n : Nat} (s : State W E n) :
    Option (W ⊕ (Fin (n + 1) × E)) × State W E n :=
  let result := (Inbox.Priority.next s.phase popWrite popEvent).run (s.writes, s.inbox)
  (result.1.1, ⟨result.2.1, result.2.2, result.1.2⟩)

def rank {W E : Type} {n : Nat} (s : State W E n) (target : Fin (n + 1)) : Nat :=
  4 * distance s.inbox.cursor target + s.phase.val + 1

theorem step_write {W E : Type} {n : Nat} (w : W) (ws : List W)
    (inbox : Ingress.State E n) (phase : Inbox.Priority.Slot) (h : phase.val ≠ 0) :
    step ⟨w :: ws, inbox, phase⟩ =
      (some (.inl w), ⟨ws, inbox, Inbox.Priority.advance phase⟩) := by
  simp [step, Inbox.Priority.next, Inbox.next, Inbox.Priority.localFirst, h, popWrite]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem step_event {W E : Type} {n : Nat} (ws : List W)
    (inbox : Ingress.State E n) (phase : Inbox.Priority.Slot)
    (source : Fin (n + 1)) (value : E)
    (h : phase.val = 0) (he : inbox.poll.1 = some (source, value)) :
    step ⟨ws, inbox, phase⟩ =
      (some (.inr (source, value)), ⟨ws, inbox.poll.2, Inbox.Priority.advance phase⟩) := by
  simp [step, Inbox.Priority.next, Inbox.next, Inbox.Priority.localFirst, h, popEvent, he]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem step_only_event {W E : Type} {n : Nat}
    (inbox : Ingress.State E n) (phase : Inbox.Priority.Slot)
    (source : Fin (n + 1)) (value : E) (he : inbox.poll.1 = some (source, value)) :
    step (⟨[], inbox, phase⟩ : State W E n) =
      (some (.inr (source, value)), ⟨[], inbox.poll.2, Inbox.Priority.advance phase⟩) := by
  by_cases h : phase.val = 0
  · exact step_event [] inbox phase source value h he
  · simp [step, Inbox.Priority.next, Inbox.next, Inbox.Priority.localFirst, h, popWrite, popEvent, he]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem poll_exists {E : Type} {n : Nat} (inbox : Ingress.State E n)
    (target : Fin (n + 1)) (value : E) (ready : inbox.slots[target.val] = some value) :
    ∃ source selected, inbox.poll.1 = some (source, selected) := by
  obtain ⟨source, selected, next, hs, _, _⟩ :=
    scan_ready inbox.slots target value ready (n + 1) inbox.cursor (distance_lt _ _)
  exact ⟨source, selected, by simp [Ingress.State.poll, hs]⟩

/-- One actual combined turn serves an occupied peer mailbox or strictly
reduces its rank. Local work is still preferred in three of four phases. -/
theorem step_progress {W E : Type} {n : Nat} (s : State W E n)
    (target : Fin (n + 1)) (value : E) (ready : s.inbox.slots[target.val] = some value) :
    (step s).1 = some (.inr (target, value)) ∨
      ((step s).2.inbox.slots[target.val] = some value ∧
        rank (step s).2 target < rank s target) := by
  rcases s with ⟨writes, inbox, phase⟩
  obtain ⟨source, selected, he⟩ := poll_exists inbox target value ready
  have hp := poll_progress inbox target value ready
  have hn := (Inbox.Priority.advance phase).isLt
  have eventProgress :
      some (Sum.inr (source, selected) : W ⊕ (Fin (n + 1) × E)) = some (.inr (target, value)) ∨
        ((inbox.poll).2.slots[target.val] = some value ∧
          4 * distance inbox.poll.2.cursor target + (Inbox.Priority.advance phase).val + 1 <
            4 * distance inbox.cursor target + phase.val + 1) := by
    rcases hp with hs | ⟨hr, hb⟩
    · left
      have hpair : (source, selected) = (target, value) := Option.some.inj (he.symm.trans hs)
      rw [hpair]
    · exact Or.inr ⟨hr, by omega⟩
  by_cases hz : phase.val = 0
  · rw [step_event writes inbox phase source selected hz he]
    exact eventProgress
  · cases writes with
    | nil =>
      rw [step_only_event inbox phase source selected he]
      exact eventProgress
    | cons w writes =>
      rw [step_write w writes inbox phase hz]
      right
      refine ⟨ready, ?_⟩
      have := Inbox.Priority.advance_positive phase hz
      simp only [rank]
      omega

def State.arrivals {W E : Type} {n : Nat} (s : State W E n) (writes : List W)
    (offers : List (Fin (n + 1) × E)) : State W E n :=
  { s with writes := s.writes ++ writes, inbox := s.inbox.arrivals offers }

structure Run (W E : Type) (n : Nat) where
  state : Nat → State W E n
  writes : Nat → List W
  events : Nat → List (Fin (n + 1) × E)
  next : ∀ i, state (i + 1) = ((step (state i)).2.arrivals (writes i) (events i))

def Run.selected {W E : Type} {n : Nat} (r : Run W E n) (i : Nat) := (step (r.state i)).1

theorem served {W E : Type} {n : Nat} (r : Run W E n) (bound : Nat) :
    ∀ i target value,
      (r.state i).inbox.slots[target.val] = some value →
      rank (r.state i) target ≤ bound →
      ∃ j, i ≤ j ∧ j < i + bound ∧ r.selected j = some (.inr (target, value)) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro i target value ready hb
    rcases step_progress (r.state i) target value ready with hs | ⟨hp, hd⟩
    · have positive : 0 < rank (r.state i) target := by simp [rank]
      exact ⟨i, Nat.le_refl _, by omega, hs⟩
    · have ha := Ingress.arrivals_preserve (step (r.state i)).2.inbox (r.events i) target value hp
      have hr : (r.state (i + 1)).inbox.slots[target.val] = some value := by
        rw [r.next]; exact ha.1
      have hrank : rank (r.state (i + 1)) target = rank (step (r.state i)).2 target := by
        rw [r.next]; simp only [rank, State.arrivals, ha.2]
      obtain ⟨j, hj, hbound, hs⟩ := ih (rank (step (r.state i)).2 target) (by omega)
        (i + 1) target value hr (by simp only [hrank, Nat.le_refl])
      exact ⟨j, by omega, by omega, hs⟩

/-- The actual nested selector serves a ready peer within 4 * mailboxCount
completed loop polls, regardless of all other peer and local arrivals. -/
theorem source_within {W E : Type} {n : Nat} (r : Run W E n) (i : Nat)
    (target : Fin (n + 1)) (value : E)
    (ready : (r.state i).inbox.slots[target.val] = some value) :
    ∃ j, i ≤ j ∧ j < i + 4 * (n + 1) ∧ r.selected j = some (.inr (target, value)) := by
  apply served r (4 * (n + 1)) i target value ready
  have := distance_lt (r.state i).inbox.cursor target
  have := (r.state i).phase.isLt
  simp only [rank]
  omega

theorem step_empty_event {W E : Type} {n : Nat} (w : W) (ws : List W)
    (inbox : Ingress.State E n) (phase : Inbox.Priority.Slot)
    (h : phase.val = 0) (he : inbox.poll.1 = none) :
    step ⟨w :: ws, inbox, phase⟩ =
      (some (.inl w), ⟨ws, inbox.poll.2, Inbox.Priority.advance phase⟩) := by
  simp [step, Inbox.Priority.next, Inbox.next, Inbox.Priority.localFirst, h, popEvent, popWrite, he]
  exact ⟨rfl, rfl, rfl, rfl⟩

inductive Waiting {W E : Type} {n : Nat} : State W E n → W → Nat → Prop
  | write (s : State W E n) (pre post : List W) (w : W)
      (h : s.writes = pre ++ w :: post) :
      Waiting s w (2 * pre.length + if s.phase.val = 0 then 2 else 1)

/-- The inner peer policy cannot take the three local-preferred slots. -/
theorem write_progress {W E : Type} {n : Nat} {s : State W E n} {w : W} {bound : Nat}
    (h : Waiting s w bound) (writes : List W) (events : List (Fin (n + 1) × E)) :
    (step s).1 = some (.inl w) ∨
      ∃ k < bound, Waiting ((step s).2.arrivals writes events) w k := by
  cases h with
  | write pre post w h =>
    rcases s with ⟨oldWrites, inbox, phase⟩
    dsimp at h
    subst oldWrites
    by_cases hz : phase.val = 0
    · cases he : inbox.poll.1 with
      | none =>
        cases pre with
        | nil =>
          exact Or.inl (by simpa only [List.nil_append] using
            (congrArg Prod.fst (step_empty_event w post inbox phase hz he)))
        | cons p pre =>
          rw [show (p :: pre) ++ w :: post = p :: (pre ++ w :: post) from rfl,
            step_empty_event p _ inbox phase hz he]
          right
          refine ⟨2 * pre.length + 1, by simp [hz]; omega, ?_⟩
          simpa [State.arrivals, Inbox.Priority.advance_at_zero phase hz,
            Inbox.Priority.first, List.append_assoc] using
            Waiting.write (⟨(pre ++ w :: post) ++ writes, inbox.poll.2.arrivals events,
              Inbox.Priority.advance phase⟩ : State W E n)
              pre (post ++ writes) w (by simp [List.append_assoc])
      | some event =>
        rw [step_event _ inbox phase event.1 event.2 hz he]
        right
        refine ⟨2 * pre.length + 1, by simp [hz], ?_⟩
        simpa [State.arrivals, Inbox.Priority.advance_at_zero phase hz,
          Inbox.Priority.first, List.append_assoc] using
          Waiting.write (⟨(pre ++ w :: post) ++ writes, inbox.poll.2.arrivals events,
            Inbox.Priority.advance phase⟩ : State W E n)
            pre (post ++ writes) w (by simp [List.append_assoc])
    · cases pre with
      | nil =>
        exact Or.inl (by simpa only [List.nil_append] using
          (congrArg Prod.fst (step_write w post inbox phase hz)))
      | cons p pre =>
        rw [show (p :: pre) ++ w :: post = p :: (pre ++ w :: post) from rfl,
          step_write p _ inbox phase hz]
        right
        refine ⟨2 * pre.length + if (Inbox.Priority.advance phase).val = 0 then 2 else 1,
          by simp only [List.length_cons, hz, ite_false]; split <;> omega, ?_⟩
        apply Waiting.write _ pre (post ++ writes) w
        simp [State.arrivals, List.append_assoc]

theorem write_served {W E : Type} {n : Nat} (r : Run W E n) (bound : Nat) :
    ∀ i w, Waiting (r.state i) w bound →
      ∃ j, i ≤ j ∧ j < i + bound ∧ r.selected j = some (.inl w) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro i w hw
    rcases write_progress hw (r.writes i) (r.events i) with hs | ⟨k, hk, hw'⟩
    · have hb : 0 < bound := by cases hw; split <;> omega
      exact ⟨i, Nat.le_refl _, by omega, hs⟩
    · rw [← r.next i] at hw'
      obtain ⟨j, hj, hb, hs⟩ := ih k hk (i + 1) w hw'
      exact ⟨j, by omega, by omega, hs⟩

/-- Local writes retain their original bound after per-peer fairness is
added: at most one network turn can precede an already queued local head. -/
theorem write_within {W E : Type} {n : Nat} (r : Run W E n) (i : Nat)
    (pre post : List W) (w : W) (h : (r.state i).writes = pre ++ w :: post) :
    ∃ j, i ≤ j ∧ j < i + 2 * (pre.length + 1) ∧ r.selected j = some (.inl w) := by
  obtain ⟨j, hj, hb, hs⟩ := write_served r _ i w (Waiting.write _ pre post w h)
  refine ⟨j, hj, ?_, hs⟩
  split at hb <;> omega

end Engine.Sync.Ingress.Prioritized
