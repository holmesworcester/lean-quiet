/-
What the verdicts should be, declaratively: the least fixpoint of
`judge` over a set of ops. `specAt n x` is x's verdict when every
derivation is at most n deep; an op's verdict is `Spec` if some depth
reaches it. An op on a requirement cycle, or above a missing op, never
gets one: it stays Unresolved, as in the engine.
-/
import engine.core.Core

namespace Engine

variable {F : Type} (fam : Family F)

def specAt (ops : Id → Option Op) : Nat → Id → Option (Verdict F)
  | 0, _ => none
  | n + 1, x => match ops x with
    | none => none
    | some o => judge fam o (o.reqs.map (specAt ops n))

/-- x's verdict among ops. -/
def Spec (ops : Id → Option Op) (x : Id) (v : Verdict F) : Prop :=
  ∃ n, specAt fam ops n x = some v

end Engine
