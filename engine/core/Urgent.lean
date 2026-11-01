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

/-- Whether o is judged ahead: the family's urgent kinds, and every op not
shared. -/
def urgentOf (o : Op) : Bool :=
  fam.urgent o || match fam.scope o with
    | .shared _ => false
    | _ => true

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

end Engine
