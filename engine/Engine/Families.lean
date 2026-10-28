/-
Several op families in one store. An application's families are
composed into one: each op belongs to the family whose kinds include its
kind, and its verdict is that family's. Kinds are disjoint by
declaration, until the registry names them (kind = sha256 of the op
type's name).

A family may read another family's facts. The connection family reads
the device secret that Community defines, so the second family's
validator sees the facts of both. The first family sees only its own:
an op of A that cites an op of B is never Valid. Each family's
relations keep their own names, so their keys never meet.

Law: `sum_left`. An A op whose requirements gave A facts has the same
verdict in the composed store as in A alone, so every law proven of A
alone (Community's included) speaks of A's ops in the composed store.
-/
import Engine.View
import Engine.Decl

namespace Engine
open Codec

instance {A B} [Codec A] [Codec B] : Codec (A ⊕ B) where
  enc | .inl a => 0 :: enc a | .inr b => 1 :: enc b
  dec
    | 0 :: r => (dec r : Option (A × List UInt8)).map fun (a, r) => (.inl a, r)
    | 1 :: r => (dec r : Option (B × List UInt8)).map fun (b, r) => (.inr b, r)
    | _ => none
  round x rest := by
    cases x <;> simp [Codec.round]
  encInto buf
    | .inl a => encInto (buf.push 0) a
    | .inr b => encInto (buf.push 1) b
  encInto_eq buf x := by cases x <;> simp [encInto_tag]
  decFrom b i := match b[i]? with
    | some 0 => decFromAs (β := A ⊕ B) .inl b (i + 1)
    | some 1 => decFromAs (β := A ⊕ B) .inr b (i + 1)
    | _ => none
  decFrom_at x h := by
    cases x <;> (simp only [h.tag]; exact decFromAs_tag _ h)

instance {A B} [SortKey A] [SortKey B] : SortKey (A ⊕ B) where
  sortOf | .inl a => SortKey.sortOf a | .inr b => SortKey.sortOf b

/-- Fresh secrets, where a family needs them (ephemeral keys): the
OS's random bytes on a device, a counter on the model, so a run of the
model is a pure function of its inputs. -/
class Fresh (m : Type → Type) where
  fresh : m ByteArray

/-- A family that reads facts of type A as well as its own. -/
structure Family₂ (A B : Type) where
  validate : Op → List (A ⊕ B) → Option B
  keys : B → List ByteArray
  scope : Op → Scope
  order : Op → Nat := fun _ => 0
  /-- The kinds this family's ops have. -/
  owns : UInt8 → Bool

/-- The A facts of a list, if every one is A's. -/
def lefts {A B} (fs : List (A ⊕ B)) : Option (List A) :=
  fs.mapM fun | .inl a => some a | .inr _ => none

/-- A and B in one store. -/
def Family.sum {A B : Type} (a : Family A) (b : Family₂ A B) : Family (A ⊕ B) where
  validate o fs :=
    if b.owns o.kind then (b.validate o fs).map .inr
    else (lefts fs).bind fun xs => (a.validate o xs).map .inl
  keys | .inl x => a.keys x | .inr y => b.keys y
  scope o := if b.owns o.kind then b.scope o else a.scope o
  order o := if b.owns o.kind then b.order o else a.order o

theorem lefts_map {A B} (fs : List A) : lefts (fs.map (.inl : A → A ⊕ B)) = some fs := by
  induction fs with
  | nil => rfl
  | cons a t ih => simp only [lefts, List.map_cons, List.mapM_cons] at *; simp [ih]

/-- **The first family's verdicts are unchanged.** -/
theorem sum_left {A B : Type} (a : Family A) (b : Family₂ A B) (o : Op) (fs : List A)
    (h : b.owns o.kind = false) :
    (Family.sum a b).validate o (fs.map .inl) = (a.validate o fs).map .inl := by
  simp [Family.sum, h, lefts_map]

theorem sum_scope_left {A B : Type} (a : Family A) (b : Family₂ A B) (o : Op)
    (h : b.owns o.kind = false) : (Family.sum a b).scope o = a.scope o := by
  simp [Family.sum, h]

/-- A view of A's lists, run in a store of A and B: each answer keeps
its A rows. -/
def View.liftL {A B α : Type} : View A α → View (A ⊕ B) α
  | .pure a => .pure a
  | .list q k => .list q fun ans =>
    (k ⟨ans.rows.filterMap fun (p, f) => match f with | .inl x => some (p, x) | .inr _ => none,
      ans.inRange, ans.total⟩).liftL

/-- The B rows of an answer. -/
def Answer.rights {A B : Type} (ans : Answer (A ⊕ B)) : List (Pos × B) :=
  ans.rows.filterMap fun (p, f) => match f with | .inr y => some (p, y) | .inl _ => none

/-- The A rows of an answer. -/
def Answer.lefts {A B : Type} (ans : Answer (A ⊕ B)) : List (Pos × A) :=
  ans.rows.filterMap fun (p, f) => match f with | .inl x => some (p, x) | .inr _ => none

end Engine
