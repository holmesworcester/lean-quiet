import engine.wire.IngressPriorityLaws

namespace Engine.Sync.Ingress

def State.cancelAll {α : Type} {n : Nat} (s : State α n)
    (sources : List (Fin (n + 1))) : State α n :=
  sources.foldl State.cancel s

theorem cancel_other {α : Type} {n : Nat} (s : State α n)
    (source target : Fin (n + 1)) (h : source ≠ target) :
    (s.cancel source).slots[target.val] = s.slots[target.val] := by
  have hn : source.val ≠ target.val := fun he => h (Fin.ext he)
  simp [State.cancel, hn]

theorem cancelAll_preserves {α : Type} {n : Nat} (s : State α n)
    (sources : List (Fin (n + 1))) (target : Fin (n + 1)) (h : target ∉ sources) :
    (s.cancelAll sources).slots[target.val] = s.slots[target.val] ∧
      (s.cancelAll sources).cursor = s.cursor := by
  induction sources generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons source sources ih =>
    have hn : source ≠ target := by intro he; subst source; simp at h
    have ht : target ∉ sources := fun hm => h (List.mem_cons_of_mem source hm)
    have hp := ih (s.cancel source) ht
    exact ⟨hp.1.trans (cancel_other s source target hn), hp.2⟩

namespace Prioritized

/-- Environment events use the actual cancellation and offer cores. They
may retire/reuse any other source without moving the consumer's cursor. -/
def State.changes {W E : Type} {n : Nat} (s : State W E n) (writes : List W)
    (closed : List (Fin (n + 1))) (events : List (Fin (n + 1) × E)) : State W E n :=
  { s with writes := s.writes ++ writes, inbox := (s.inbox.cancelAll closed).arrivals events }

theorem changes_preserve {W E : Type} {n : Nat} (s : State W E n) (writes : List W)
    (closed : List (Fin (n + 1))) (events : List (Fin (n + 1) × E))
    (target : Fin (n + 1)) (value : E)
    (h : target ∉ closed) (ready : s.inbox.slots[target.val] = some value) :
    (s.changes writes closed events).inbox.slots[target.val] = some value ∧
      rank (s.changes writes closed events) target = rank s target := by
  have hc := cancelAll_preserves s.inbox closed target h
  have ha := arrivals_preserve (s.inbox.cancelAll closed) events target value (hc.1.trans ready)
  exact ⟨ha.1, by simp only [rank, State.changes, ha.2, hc.2]⟩

structure ChurnRun (W E : Type) (n : Nat) where
  state : Nat → State W E n
  writes : Nat → List W
  events : Nat → List (Fin (n + 1) × E)
  closed : Nat → List (Fin (n + 1))
  next : ∀ i, state (i + 1) =
    (step (state i)).2.changes (writes i) (closed i) (events i)

def ChurnRun.selected {W E : Type} {n : Nat} (r : ChurnRun W E n) (i : Nat) :=
  (step (r.state i)).1

theorem served_or_cancelled {W E : Type} {n : Nat} (r : ChurnRun W E n) (bound : Nat) :
    ∀ i target value,
      (r.state i).inbox.slots[target.val] = some value →
      rank (r.state i) target ≤ bound →
      ∃ j, i ≤ j ∧ j < i + bound ∧
        (r.selected j = some (.inr (target, value)) ∨ target ∈ r.closed j) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro i target value ready hb
    have positive : 0 < rank (r.state i) target := by simp [rank]
    by_cases cancelled : target ∈ r.closed i
    · exact ⟨i, Nat.le_refl _, by omega, Or.inr cancelled⟩
    rcases step_progress (r.state i) target value ready with hs | ⟨hp, hd⟩
    · exact ⟨i, Nat.le_refl _, by omega, Or.inl hs⟩
    · have hc := changes_preserve (step (r.state i)).2 (r.writes i) (r.closed i)
        (r.events i) target value cancelled hp
      have hr : (r.state (i + 1)).inbox.slots[target.val] = some value := by
        rw [r.next]; exact hc.1
      have hrank : rank (r.state (i + 1)) target = rank (step (r.state i)).2 target := by
        rw [r.next]; exact hc.2
      obtain ⟨j, hj, hbound, hs⟩ := ih (rank (step (r.state i)).2 target) (by omega)
        (i + 1) target value hr (by simp only [hrank, Nat.le_refl])
      exact ⟨j, by omega, by omega, hs⟩

/-- Even arbitrary connection churn cannot extend an owed source's bound:
it is served or that incarnation is explicitly retired within the bound. -/
theorem source_or_cancelled_within {W E : Type} {n : Nat} (r : ChurnRun W E n)
    (i : Nat) (target : Fin (n + 1)) (value : E)
    (ready : (r.state i).inbox.slots[target.val] = some value) :
    ∃ j, i ≤ j ∧ j < i + 4 * (n + 1) ∧
      (r.selected j = some (.inr (target, value)) ∨ target ∈ r.closed j) := by
  apply served_or_cancelled r (4 * (n + 1)) i target value ready
  have := distance_lt (r.state i).inbox.cursor target
  have := (r.state i).phase.isLt
  simp only [rank]
  omega

theorem Waiting.same_inputs {W E : Type} {n : Nat} {s s' : State W E n}
    {w : W} {bound : Nat} (hw : Waiting s w bound)
    (writes : s'.writes = s.writes) (phase : s'.phase = s.phase) : Waiting s' w bound := by
  cases hw with
  | write pre post w h =>
    simpa only [phase] using Waiting.write s' pre post w (writes.trans h)

theorem write_served_churn {W E : Type} {n : Nat} (r : ChurnRun W E n) (bound : Nat) :
    ∀ i w, Waiting (r.state i) w bound →
      ∃ j, i ≤ j ∧ j < i + bound ∧ r.selected j = some (.inl w) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro i w hw
    rcases write_progress hw (r.writes i) (r.events i) with hs | ⟨k, hk, hw'⟩
    · have hb : 0 < bound := by cases hw; split <;> omega
      exact ⟨i, Nat.le_refl _, by omega, hs⟩
    · have changed : Waiting (r.state (i + 1)) w k := by
        rw [r.next]
        exact hw'.same_inputs rfl rfl
      obtain ⟨j, hj, hb, hs⟩ := ih k hk (i + 1) w changed
      exact ⟨j, by omega, by omega, hs⟩

/-- Peer retirement/reuse cannot slow the local FIFO's two-turn bound. -/
theorem write_within_churn {W E : Type} {n : Nat} (r : ChurnRun W E n) (i : Nat)
    (pre post : List W) (w : W) (h : (r.state i).writes = pre ++ w :: post) :
    ∃ j, i ≤ j ∧ j < i + 2 * (pre.length + 1) ∧ r.selected j = some (.inl w) := by
  obtain ⟨j, hj, hb, hs⟩ := write_served_churn r _ i w (Waiting.write _ pre post w h)
  refine ⟨j, hj, ?_, hs⟩
  split at hb <;> omega

def ChurnRun.states {W E : Type} {n : Nat} (initial : State W E n)
    (writes : Nat → List W) (closed : Nat → List (Fin (n + 1)))
    (events : Nat → List (Fin (n + 1) × E)) : Nat → State W E n
  | 0 => initial
  | i + 1 => (step (ChurnRun.states initial writes closed events i)).2.changes
      (writes i) (closed i) (events i)

def ChurnRun.make {W E : Type} {n : Nat} (initial : State W E n)
    (writes : Nat → List W) (closed : Nat → List (Fin (n + 1)))
    (events : Nat → List (Fin (n + 1) × E)) : ChurnRun W E n :=
  { state := ChurnRun.states initial writes closed events, writes, closed, events,
    next := fun _ => rfl }

/-- A nonempty infinite witness: local input and two peer sources flood
forever; the third source is retired and immediately refilled each turn. -/
def churnFlood : ChurnRun Nat Nat 2 :=
  ChurnRun.make { writes := [0], inbox := { slots := #v[some 10, some 11, some 12] } }
    (fun i => [i + 1]) (fun _ => [⟨2, by decide⟩])
    (fun i => [(⟨0, by decide⟩, 100 + i), (⟨1, by decide⟩, 200 + i),
      (⟨2, by decide⟩, 300 + i)])

theorem churnFlood_source :
    ∃ j, 0 ≤ j ∧ j < 12 ∧ churnFlood.selected j = some (.inr (⟨1, by decide⟩, 11)) := by
  obtain ⟨j, hj, hb, hs⟩ := source_or_cancelled_within churnFlood 0 ⟨1, by decide⟩ 11 rfl
  refine ⟨j, hj, hb, ?_⟩
  rcases hs with delivered | cancelled
  · exact delivered
  · simp [churnFlood, ChurnRun.make] at cancelled

theorem churnFlood_write :
    ∃ j, 0 ≤ j ∧ j < 2 ∧ churnFlood.selected j = some (.inl 0) := by
  exact write_within_churn churnFlood 0 [] [] 0 rfl

theorem churnFlood_exact : churnFlood.selected 0 = some (.inl 0) ∧
    churnFlood.selected 7 = some (.inr (⟨1, by decide⟩, 11)) := by decide

end Prioritized
end Engine.Sync.Ingress
