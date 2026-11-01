/-
A value written as another, with no tag of its own: a family of one op
type writes its body and fact as that op type's, which carry their own
tags (app/settings/Family.lean). Its laws are the other type's, proven
once in engine/core/Codec.lean.
-/
import engine.core.Codec

namespace Engine.Codec

def via {α β} [Codec β] (to : α → β) (of : β → α) (h : ∀ a, of (to a) = a) : Codec α where
  enc a := enc (to a)
  dec r := (dec r : Option (β × List UInt8)).map fun p => (of p.1, p.2)
  round a rest := by simp [Codec.round, h]
  encInto buf a := encInto buf (to a)
  encInto_eq buf a := encInto_eq buf (to a)
  decFrom := decFromAs of
  decFrom_at a hat := by rw [decFromAs_at of hat, h]

theorem via_enc {α β} [Codec β] (to : α → β) (of : β → α) (h : ∀ a, of (to a) = a)
    (a : α) : (via to of h).enc a = enc (to a) := rfl

end Engine.Codec
