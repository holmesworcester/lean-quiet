/-
Urgent ops: membership, and every op not shared (a connection's, and a
node's own local ops). A write turn judges them ahead of the backlog, as
soon as they can be decided (engine/core/Core.lean's `urgentClose`, on
the turn's job and, transitively, the urgent ops each decision wakes), so
the store is never left with an urgent op it could judge but has not.

- `UrgentSettled`: every stored urgent op whose stored requirement closure
  is all urgent is decided, or not yet judgeable. (A bogus urgent op that
  cites content may wait behind the backlog; its verdict is never Valid,
  and every op whose closure holds it is excluded too.)
- `settled_urgent`: a store at rest (queue empty) is so.
- **`urgent_spec`**: under `Inv` and `UrgentSettled`, an urgent op whose
  closure is all urgent has exactly its spec verdict over the stored ops,
  whatever is still queued. `urgent_valid_iff` is its Valid half, the form
  trust laws cite: they read only Valid facts.
-/
import engine.core.Proofs
import engine.core.Locality

namespace Engine
variable {F : Type} (fam : Family F)

/-- Every stored op in x's requirement closure (x included) is urgent. -/
def UrgentClosed (s : DB F) (x : Id) : Prop :=
  ∀ y o, Sync.Reach s.ops x y → s.ops y = some o → urgentOf fam o = true

/-- No stored urgent op with an all-urgent closure is judgeable and
undecided. -/
def UrgentSettled (s : DB F) : Prop :=
  ∀ x o, s.ops x = some o → UrgentClosed fam s x → s.status x = none →
    judge fam o (o.reqs.map s.status) = none

variable {fam}

theorem UrgentClosed.req {s : DB F} {x r : Id} {o : Op} (h : UrgentClosed fam s x)
    (ho : s.ops x = some o) (hr : r ∈ o.reqs) : UrgentClosed fam s r :=
  fun y p hy hp => h y p (Sync.Reach.trans (.step .refl ho hr) hy) hp

/-- **A store at rest is urgently settled.** -/
theorem settled_urgent {s : DB F} (hi : Inv fam s) (hq : s.queue = []) : UrgentSettled fam s := by
  intro x o ho _ hx
  rcases hi.wait x o ho hx with h | h
  · rw [hq] at h; cases h
  · exact h.1

/-- **An urgent op whose closure is all urgent has its spec verdict**,
under `Inv` and `UrgentSettled`, whatever is still queued. -/
theorem urgent_spec {s : DB F} (hi : Inv fam s) (hu : UrgentSettled fam s) {x : Id}
    (hc : UrgentClosed fam s x) (v : Verdict F) :
    s.status x = some v ↔ Spec fam s.ops x v := by
  refine ⟨hi.sound x v, fun ⟨n, hn⟩ => ?_⟩
  suffices key : ∀ n x v, UrgentClosed fam s x → specAt fam s.ops n x = some v → s.status x = some v from
    key n x v hc hn
  intro n
  induction n with
  | zero => intro x v _ h; simp [specAt] at h
  | succ n ih =>
    intro x v hc h
    unfold specAt at h
    cases ho : s.ops x with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      have hb : Below o.reqs (specAt fam s.ops n) s.status := by
        intro r hr
        cases hsr : specAt fam s.ops n r with
        | none => exact Or.inl rfl
        | some w => exact Or.inr (ih r w (hc.req ho hr) hsr).symm
      have hj := judge_mono h hb
      cases hx : s.status x with
      | none =>
        have := hu x o ho hc hx
        rw [this] at hj; cases hj
      | some w =>
        have := spec_det (hi.sound x w hx) ⟨n + 1, by unfold specAt; rw [ho]; exact h⟩
        rw [this]

/-- **The Valid half, as trust laws cite it.** -/
theorem urgent_valid_iff {s : DB F} (hi : Inv fam s) (hu : UrgentSettled fam s) {x : Id}
    (hc : UrgentClosed fam s x) (f : F) :
    s.status x = some (.valid f) ↔ Spec fam s.ops x (.valid f) :=
  urgent_spec hi hu hc (.valid f)

/-! ## Urgent ops cite only urgent ops

A family declares which facts urgent ops make (`uf`): only urgent ops
make them, and an urgent op is Valid only citing them. Then a Valid
urgent op's whole closure is urgent (`urgent_valid_closed`), so its Valid
status is the spec's whatever is queued, with no premise on its closure
(`urgent_valid_spec`). -/

variable (fam) in
/-- The family's declaration: urgent ops cite only urgent ops' facts. -/
structure UrgentCites where
  uf : F → Bool
  fact : ∀ o fs f, fam.validate o fs = some f → uf f = true → fam.urgent o = true
  cites : ∀ o fs f, fam.urgent o = true → fam.validate o fs = some f → ∀ g ∈ fs, uf g = true

/-- judge's Valid verdict is validate's, over the requirements' Valid facts. -/
theorem judge_valid {o : Op} {sts : List (Option (Verdict F))} {f : F}
    (h : judge fam o sts = some (.valid f)) : ∃ fs, allValid sts = some fs ∧ fam.validate o fs = some f := by
  unfold judge at h
  split at h
  · cases h
  · cases ha : allValid sts with
    | none => rw [ha] at h; cases h
    | some fs =>
      rw [ha] at h
      refine ⟨fs, rfl, ?_⟩
      cases hv : fam.validate o fs with
      | none => simp [hv] at h
      | some g => simp [hv] at h; simp [h]

theorem All2.mem_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {fs : List β}, All2 R l fs →
    ∀ a ∈ l, ∃ b ∈ fs, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hr t, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hab⟩ := All2.mem_right t a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- What x reaches is x, or reached from one of its requirements. -/
theorem Sync.Reach.head {ops : Id → Option Op} {x z : Id} (h : Sync.Reach ops x z) :
    z = x ∨ ∃ o r, ops x = some o ∧ r ∈ o.reqs ∧ Sync.Reach ops r z := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ hy hr ih =>
    rcases ih with rfl | ⟨o, r', hx, hr', hreach⟩
    · exact Or.inr ⟨_, _, hy, hr, .refl⟩
    · exact Or.inr ⟨o, r', hx, hr', .step hreach hy hr⟩

/-- **A Valid urgent op's closure is all urgent.** -/
theorem urgent_valid_closed (hc : UrgentCites fam) {ops : Id → Option Op} :
    ∀ (n : Nat) (x : Id) (o : Op) (f : F), ops x = some o → fam.urgent o = true →
      specAt fam ops n x = some (.valid f) → ∀ y p, Sync.Reach ops x y → ops y = some p → fam.urgent p = true := by
  intro n
  induction n with
  | zero => intro x o f _ _ h; cases h
  | succ n ih =>
    intro x o f ho hu hs y p hy hp
    unfold specAt at hs
    rw [ho] at hs
    obtain ⟨fs, hfs, hv⟩ := judge_valid hs
    rcases hy.head with rfl | ⟨o', r, ho', hr, hry⟩
    · rw [ho] at hp; cases hp; exact hu
    · rw [ho] at ho'; cases ho'
      obtain ⟨w, hw, hrw⟩ := All2.mem_right (allValid_forall2 hfs) r hr
      have huw := hc.cites o fs f hu hv w hw
      cases n with
      | zero => cases hrw
      | succ m =>
        have hrw' := hrw
        unfold specAt at hrw'
        cases hor : ops r with
        | none => rw [hor] at hrw'; cases hrw'
        | some q =>
          rw [hor] at hrw'
          obtain ⟨fs', -, hv'⟩ := judge_valid hrw'
          exact ih r q w hor (hc.fact q fs' w hv' huw) hrw y p hry hp

/-- **An urgent op's Valid status is the spec's**, whatever is queued:
no premise on what it cites. -/
theorem urgent_valid_spec (hc : UrgentCites fam) {s : DB F} (hi : Inv fam s) (hu : UrgentSettled fam s)
    {x : Id} {o : Op} (ho : s.ops x = some o) (hx : fam.urgent o = true) (f : F) :
    s.status x = some (.valid f) ↔ Spec fam s.ops x (.valid f) := by
  refine ⟨hi.sound x _, fun hv => ?_⟩
  obtain ⟨n, hn⟩ := hv
  have hcl : UrgentClosed fam s x := fun y p hy hp => by
    simp [urgentOf, urgent_valid_closed hc n x o f ho hx hn y p hy hp]
  exact (urgent_valid_iff hi hu hcl f).2 ⟨n, hn⟩

end Engine
