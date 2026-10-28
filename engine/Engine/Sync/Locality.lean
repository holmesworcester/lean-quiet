/-
**Locality**: a decided verdict depends only on the op's requirement
closure. If a node holds every op a peer's verdict on x was reached
from (x and what it requires, recursively, among the peer's ops), the
node reaches the same verdict.

This is why a windowed node, sent its window's ops with their
requirement closures, judges each of them as its peer does: its other
ops, and the ops it lacks, cannot change those verdicts.
-/
import Engine.SpecLemmas

namespace Engine.Sync
open Classical

/-- y is x or something x requires, recursively, among these ops. -/
inductive Reach (ops : Id → Option Op) (x : Id) : Id → Prop
  | refl : Reach ops x x
  | step {y : Id} {o : Op} {r : Id} : Reach ops x y → ops y = some o → r ∈ o.reqs → Reach ops x r

theorem Reach.trans {ops : Id → Option Op} {x y z : Id} (h1 : Reach ops x y) (h2 : Reach ops y z) :
    Reach ops x z := by
  induction h2 with
  | refl => exact h1
  | step _ hy hr ih => exact .step ih hy hr

/-- The ops restricted to those satisfying P. -/
noncomputable def restrict (ops : Id → Option Op) (P : Id → Prop) : Id → Option Op :=
  fun y => if P y then ops y else none

section
variable {F : Type} (fam : Family F)

/-- A verdict reads only the closure: restricting the ops to anything
containing x's closure changes nothing at any depth. -/
theorem specAt_restrict (ops : Id → Option Op) :
    ∀ (n : Nat) (x : Id) (P : Id → Prop), (∀ y, Reach ops x y → P y) →
      specAt fam (restrict ops P) n x = specAt fam ops n x := by
  intro n
  induction n with
  | zero => intro x P _; rfl
  | succ n ih =>
    intro x P hP
    simp only [specAt]
    have hx : restrict ops P x = ops x := by simp [restrict, hP x .refl]
    rw [hx]
    cases ho : ops x with
    | none => rfl
    | some o =>
      have e : o.reqs.map (specAt fam (restrict ops P) n) = o.reqs.map (specAt fam ops n) :=
        List.map_congr_left fun r hr => ih r P (fun y hy => hP y (Reach.trans (.step .refl ho hr) hy))
      simp only [e]

/-- **Locality.** If this node holds every op the peer's verdict on x
was reached from, it reaches the same verdict. -/
theorem spec_local {ops ops' : Id → Option Op} {x : Id} {v : Verdict F}
    (h : Spec fam ops x v) (hold : ∀ y o, Reach ops x y → ops y = some o → ops' y = some o) :
    Spec fam ops' x v := by
  obtain ⟨n, hn⟩ := h
  have hr : Spec fam (restrict ops (Reach ops x)) x v :=
    ⟨n, by rw [specAt_restrict fam ops n x (Reach ops x) (fun _ h => h)]; exact hn⟩
  refine spec_extends (fam := fam) ?_ hr
  intro y o hy
  simp only [restrict] at hy
  split at hy
  · rename_i hreach; exact hold y o hreach hy
  · cases hy

end

end Engine.Sync
