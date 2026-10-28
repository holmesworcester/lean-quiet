/-
Several op families in one store. An application's families are
composed into one: each op belongs to the family whose kinds include its
kind, and its verdict is that family's. Kinds are disjoint by
declaration (until the registry names them: kind = sha256 of the op
type's name).

A family may read another family's facts. The Connection family reads
the device secret that Community defines, so a composed family's
validator sees the facts of both. The first family sees only its own:
an op of A that cites an op of B is never Valid.

Law (stated): `sum_left`. An A op whose requirements are all A ops has
the same verdict in the composed store as in A alone. So every law
proven of A alone, Community's included, holds of A's ops in the
composed store.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Engine.Core

namespace Engine

/-- A family that reads facts of type A as well as its own. -/
structure Family₂ (A B : Type) where
  validate : Op → List (A ⊕ B) → Option B
  keys : B → List ByteArray
  scope : Op → Scope
  order : Op → Nat := fun _ => 0
  /-- The kinds this family's ops have. -/
  owns : UInt8 → Bool

/-- A and B in one store. -/
def Family.sum {A B : Type} (a : Family A) (b : Family₂ A B) : Family (A ⊕ B) := sorry

/-- **The first family's verdicts are unchanged.** -/
theorem sum_left {A B : Type} (a : Family A) (b : Family₂ A B) (o : Op) (fs : List A)
    (h : b.owns o.kind = false) :
    (Family.sum a b).validate o (fs.map .inl) = (a.validate o fs).map .inl := sorry

end Engine
