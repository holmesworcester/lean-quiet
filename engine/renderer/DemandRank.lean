import engine.renderer.Demand

namespace Demand
variable {K : Type} [BEq K] [LawfulBEq K]
set_option linter.unusedSectionVars false

/-- Selecting job records is exactly selection of their runtime keys. -/
theorem next_map {V : Type} (key : V → K) (visible : K → Bool) (background : Bool)
    (queued : List V) :
    next visible background (queued.map key) =
      (next (fun v => visible (key v)) background queued).map key := by
  simp only [next, List.find?_map]
  cases found : queued.find? (fun v => visible (key v)) with
  | none => cases background <;> simp [Function.comp_def, found]
  | some value => simp [Function.comp_def, found]

theorem takeBy_map {V : Type} (key : V → K) (visible : K → Bool) (background : Bool)
    (queued : List V) :
    ((takeBy key visible background queued).1.map key,
      (takeBy key visible background queued).2.map key) =
      take visible background (queued.map key) := by
  simp only [take, takeBy, id_eq]
  rw [next_map]
  cases found : next (fun v => visible (key v)) background queued with
  | none => simp
  | some value => simp [List.filter_map, Function.comp_def]

/-- Filtering predecessors cannot move retained work backwards. -/
theorem filter_rank (keep : K → Bool) (queued : List K) (target : K)
    (present : target ∈ queued) (retained : keep target = true) :
    (queued.filter keep).idxOf target ≤ queued.idxOf target := by
  induction queued with
  | nil => cases present
  | cons head tail ih =>
    by_cases same : head = target
    · subst head; simp [retained]
    · have hit : target ∈ tail := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      have h := ih hit
      by_cases kept : keep head = true
      · simpa [kept, List.idxOf_cons, same] using h
      · simp [kept, List.idxOf_cons, same]
        omega

/-- One actual visible-first selection either chooses the target or reduces
its queue rank. The rank counts all predecessors, including background work. -/
theorem take_progress (visible : K → Bool) (background : Bool) (queued : List K)
    (target : K) (present : target ∈ queued) (ready : visible target = true) :
    (take visible background queued).1 = some target ∨
      target ∈ (take visible background queued).2 ∧
      (take visible background queued).2.idxOf target < queued.idxOf target := by
  induction queued with
  | nil => cases present
  | cons head tail ih =>
    by_cases hv : visible head = true
    · by_cases same : head = target
      · subst head; left; simp [take, takeBy, next, hv]
      · right
        have hit : target ∈ tail := (List.mem_cons.mp present).resolve_left (Ne.symm same)
        have retained : (target != head) = true := by simp [Ne.symm same]
        have rank := filter_rank (fun k => k != head) tail target hit retained
        simp only [take, takeBy, next, List.find?_cons, hv, ↓reduceIte, id_eq,
          List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        constructor
        · exact List.mem_filter.mpr ⟨hit, retained⟩
        · simpa [List.idxOf_cons, same] using Nat.lt_succ_of_le rank
    · have found : ∃ selected, tail.find? visible = some selected := by
        cases h : tail.find? visible with
        | some selected => exact ⟨selected, rfl⟩
        | none =>
          have hit : target ∈ tail := (List.mem_cons.mp present).resolve_left (by intro e; subst head; exact hv ready)
          exact False.elim ((List.find?_eq_none.mp h target hit) ready)
      obtain ⟨selected, hs⟩ := found
      have selectedVisible := List.find?_some hs
      have different : head ≠ selected := by intro e; subst head; exact hv selectedVisible
      have hit : target ∈ tail := (List.mem_cons.mp present).resolve_left (by intro e; subst head; exact hv ready)
      have same : head ≠ target := by intro e; subst head; exact hv ready
      have eq : take visible background (head :: tail) =
          ((take visible background tail).1, head :: (take visible background tail).2) := by
        simp [take, takeBy, next, hv, hs, different]
      rw [eq]
      rcases ih hit with chosen | smaller
      · exact Or.inl chosen
      · right
        refine ⟨List.mem_cons_of_mem _ smaller.1, ?_⟩
        simp [List.idxOf_cons, same]
        exact smaller.2

/-- Arbitrary removals and later FIFO admissions cannot defeat that decrease. -/
theorem take_changes (visible : K → Bool) (background : Bool) (queued added : List K)
    (keep : K → Bool) (target : K) (present : target ∈ queued)
    (ready : visible target = true) (retained : keep target = true) :
    (take visible background queued).1 = some target ∨
      target ∈ (take visible background queued).2.filter keep ++ added ∧
      ((take visible background queued).2.filter keep ++ added).idxOf target < queued.idxOf target := by
  rcases take_progress visible background queued target present ready with chosen | progress
  · exact Or.inl chosen
  · right
    have mem : target ∈ (take visible background queued).2.filter keep :=
      List.mem_filter.mpr ⟨progress.1, retained⟩
    refine ⟨List.mem_append_left _ mem, ?_⟩
    have rank := filter_rank keep (take visible background queued).2 target progress.1 retained
    simpa [List.idxOf_append, mem] using Nat.lt_of_le_of_lt rank progress.2

/-- An attempted selection is one transition, even if its action is canceled
before IO or publication. Later visibility and finite arrivals are arbitrary. -/
structure SelectionRun (K : Type) [BEq K] where
  queue : Nat → List K
  visible : Nat → K → Bool
  background : Nat → Bool
  keep : Nat → K → Bool
  added : Nat → List K
  next : ∀ n, queue (n+1) =
    (take (visible n) (background n) (queue n)).2.filter (keep n) ++ added n

/-- A continuously visible queued key is selected or explicitly retired within
one more attempted step than its initial number of queued predecessors. No
fairness premise, quiescence or bound on later arrivals is used. -/
theorem selected_or_retired (r : SelectionRun K) : ∀ rank i target,
    (r.queue i).idxOf target = rank → target ∈ r.queue i →
    (∀ j, i ≤ j → j < i + rank + 1 → target ∈ r.queue j → r.visible j target = true) →
    ∃ j, i ≤ j ∧ j < i + rank + 1 ∧
      ((take (r.visible j) (r.background j) (r.queue j)).1 = some target ∨ r.keep j target = false) := by
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro i target hr present ready
    by_cases keep : r.keep i target = true
    · rcases take_changes (r.visible i) (r.background i) (r.queue i) (r.added i)
        (r.keep i) target present (ready i (Nat.le_refl _) (by omega) present) keep with chosen | progress
      · exact ⟨i, Nat.le_refl _, by omega, Or.inl chosen⟩
      · rw [← r.next i] at progress
        obtain ⟨j, hji, hj, selected⟩ := ih _ (by omega) (i+1) target rfl progress.1
          (fun j hj bound mem => ready j (by omega) (by omega) mem)
        exact ⟨j, by omega, by omega, selected⟩
    · exact ⟨i, Nat.le_refl _, by omega, Or.inr (by simpa using keep)⟩

/-- With continued ownership, the retirement alternative is impossible. -/
theorem selected_within (r : SelectionRun K) (i : Nat) (target : K)
    (present : target ∈ r.queue i)
    (ready : ∀ j, i ≤ j → j < i + (r.queue i).idxOf target + 1 →
      target ∈ r.queue j → r.visible j target = true)
    (retained : ∀ j, i ≤ j → j < i + (r.queue i).idxOf target + 1 → r.keep j target = true) :
    ∃ j, i ≤ j ∧ j < i + (r.queue i).idxOf target + 1 ∧ (take (r.visible j) (r.background j) (r.queue j)).1 = some target := by
  obtain ⟨j, lower, upper, chosen | retired⟩ :=
    selected_or_retired r _ i target rfl present ready
  · exact ⟨j, lower, upper, chosen⟩
  · rw [retained j lower upper] at retired
    cases retired

end Demand
