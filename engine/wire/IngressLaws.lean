import engine.wire.Ingress

namespace Engine.Sync.Ingress

theorem distance_lt {n : Nat} (cursor target : Fin (n + 1)) :
    distance cursor target < n + 1 := by
  have := cursor.isLt
  have := target.isLt
  simp only [distance]
  split <;> omega

theorem distance_zero {n : Nat} (cursor target : Fin (n + 1)) :
    distance cursor target = 0 ↔ cursor = target := by
  have := cursor.isLt
  have := target.isLt
  simp only [distance, Fin.ext_iff]
  split <;> omega

theorem advance_distance {n : Nat} (cursor target : Fin (n + 1))
    (h : cursor ≠ target) :
    distance (advance cursor) target + 1 = distance cursor target := by
  have hc := cursor.isLt
  have ht := target.isLt
  have hn : cursor.val ≠ target.val := fun he => h (Fin.ext he)
  simp only [advance, distance]
  split <;> simp only <;> split <;> split <;> omega

/-- If a source is ready within the remaining scan, the poll cannot return
empty or pass that source. Every other selected source reduces its rank. -/
theorem scan_ready {α : Type} {n : Nat} (slots : Vector (Option α) (n + 1))
    (target : Fin (n + 1)) (value : α) (ready : slots[target.val] = some value) :
    ∀ fuel cursor, distance cursor target < fuel →
      ∃ source selected next,
        scan slots fuel cursor = (some (source, selected), next) ∧
        slots[source.val] = some selected ∧
        (source = target ∨ distance next target < distance cursor target) := by
  intro fuel
  induction fuel with
  | zero => intro cursor h; omega
  | succ fuel ih =>
    intro cursor h
    cases hc : slots[cursor.val] with
    | some v =>
      refine ⟨cursor, v, advance cursor, by simp [scan, hc], hc, ?_⟩
      by_cases ht : cursor = target
      · exact Or.inl ht
      · right
        have := advance_distance cursor target ht
        omega
    | none =>
      have ht : cursor ≠ target := by
        intro he
        subst cursor
        simp [hc] at ready
      have hd := advance_distance cursor target ht
      obtain ⟨source, selected, next, hs, hv, hb⟩ :=
        ih (advance cursor) (by omega)
      refine ⟨source, selected, next, by simpa [scan, hc] using hs, hv, ?_⟩
      rcases hb with he | hb
      · exact Or.inl he
      · exact Or.inr (by omega)

theorem scan_selected {α : Type} {n : Nat} (slots : Vector (Option α) (n + 1))
    (fuel : Nat) (cursor source next : Fin (n + 1)) (value : α)
    (h : scan slots fuel cursor = (some (source, value), next)) :
    slots[source.val] = some value := by
  induction fuel generalizing cursor with
  | zero => simp [scan] at h
  | succ fuel ih =>
    cases hc : slots[cursor.val] with
    | none => exact ih _ (by simpa [scan, hc] using h)
    | some v =>
      simp only [scan, hc, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, _⟩ := h
      exact hc

theorem offer_preserves {α : Type} {n : Nat} (s : State α n)
    (source target : Fin (n + 1)) (value held : α)
    (h : s.slots[target.val] = some held) :
    (s.offer source value).2.slots[target.val] = some held ∧
      (s.offer source value).2.cursor = s.cursor := by
  cases hs : s.slots[source.val] with
  | some v => simp [State.offer, hs, h]
  | none =>
    have hn : source.val ≠ target.val := by
      intro he
      have : source = target := Fin.ext he
      subst source
      simp [hs] at h
    simp [State.offer, hs, hn, h]

/-- One production poll serves an occupied mailbox or preserves its value
and strictly decreases its finite distance, regardless of all other slots. -/
theorem poll_progress {α : Type} {n : Nat} (s : State α n)
    (target : Fin (n + 1)) (value : α)
    (ready : s.slots[target.val] = some value) :
    (s.poll).1 = some (target, value) ∨
      ((s.poll).2.slots[target.val] = some value ∧
        distance (s.poll).2.cursor target < distance s.cursor target) := by
  obtain ⟨source, selected, next, hs, hv, hb⟩ :=
    scan_ready s.slots target value ready (n + 1) s.cursor (distance_lt _ _)
  simp only [State.poll, hs]
  rcases hb with he | hb
  · subst source
    have : selected = value := by simpa [ready] using hv.symm
    subst selected
    exact Or.inl rfl
  · by_cases he : source = target
    · subst source
      have : selected = value := by simpa [ready] using hv.symm
      subst selected
      exact Or.inl rfl
    · right
      have hn : source.val ≠ target.val := fun h => he (Fin.ext h)
      exact ⟨by simp [hn, ready], hb⟩

def State.arrivals {α : Type} {n : Nat} (s : State α n)
    (offers : List (Fin (n + 1) × α)) : State α n :=
  offers.foldl (fun s (source, value) => (s.offer source value).2) s

theorem arrivals_preserve {α : Type} {n : Nat} (s : State α n)
    (offers : List (Fin (n + 1) × α)) (target : Fin (n + 1)) (held : α)
    (h : s.slots[target.val] = some held) :
    (s.arrivals offers).slots[target.val] = some held ∧
      (s.arrivals offers).cursor = s.cursor := by
  induction offers generalizing s with
  | nil => exact ⟨h, rfl⟩
  | cons offer rest ih =>
    have hp := offer_preserves s offer.1 target offer.2 held h
    have hr := ih (s.offer offer.1 offer.2).2 hp.1
    exact ⟨hr.1, hr.2.trans hp.2⟩

structure Run (α : Type) (n : Nat) where
  state : Nat → State α n
  arrivals : Nat → List (Fin (n + 1) × α)
  next : ∀ i, state (i + 1) = ((state i).poll).2.arrivals (arrivals i)

def Run.selected {α : Type} {n : Nat} (r : Run α n) (i : Nat) :=
  (r.state i).poll.1

/-- No producer fairness premise: arbitrarily many new offers may occur
between completed polls, including offers to every other occupied source. -/
theorem served {α : Type} {n : Nat} (r : Run α n) (bound : Nat) :
    ∀ i target value,
      (r.state i).slots[target.val] = some value →
      distance (r.state i).cursor target < bound →
      ∃ j, i ≤ j ∧ j < i + bound ∧ r.selected j = some (target, value) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro i target value ready hb
    rcases poll_progress (r.state i) target value ready with hs | ⟨hp, hd⟩
    · exact ⟨i, Nat.le_refl _, by omega, hs⟩
    · have ha := arrivals_preserve ((r.state i).poll).2 (r.arrivals i) target value hp
      have hr : (r.state (i + 1)).slots[target.val] = some value := by
        rw [r.next]; exact ha.1
      have hc : (r.state (i + 1)).cursor = ((r.state i).poll).2.cursor := by
        rw [r.next]; exact ha.2
      obtain ⟨j, hj, hbound, hs⟩ :=
        ih (distance ((r.state i).poll).2.cursor target + 1) (by omega)
          (i + 1) target value hr (by rw [hc]; omega)
      exact ⟨j, by omega, by omega, hs⟩

/-- A ready source is served in at most the fixed mailbox count, even if
all other sources flood forever. This bound counts completed network polls. -/
theorem source_within {α : Type} {n : Nat} (r : Run α n) (i : Nat)
    (target : Fin (n + 1)) (value : α)
    (ready : (r.state i).slots[target.val] = some value) :
    ∃ j, i ≤ j ∧ j < i + (n + 1) ∧ r.selected j = some (target, value) :=
  served r (n + 1) i target value ready (distance_lt _ _)

def states {α : Type} {n : Nat} (initial : State α n)
    (arrivals : Nat → List (Fin (n + 1) × α)) : Nat → State α n
  | 0 => initial
  | i + 1 => ((states initial arrivals i).poll).2.arrivals (arrivals i)

def run {α : Type} {n : Nat} (initial : State α n)
    (arrivals : Nat → List (Fin (n + 1) × α)) : Run α n :=
  { state := states initial arrivals, arrivals, next := fun _ => rfl }

/-- An infinite execution keeps every source busy; none needs a quiet gap. -/
def flooded : Run Nat 2 :=
  run { slots := #v[some 0, some 1, some 2] }
    (fun i => [(⟨0, by decide⟩, 3 * i + 3),
      (⟨1, by decide⟩, 3 * i + 4), (⟨2, by decide⟩, 3 * i + 5)])

theorem flooded_prefix :
    ((List.range 9).map fun i => flooded.selected i |>.map (·.1.val)) =
      [some 0, some 1, some 2, some 0, some 1, some 2, some 0, some 1, some 2] := by
  decide

end Engine.Sync.Ingress
