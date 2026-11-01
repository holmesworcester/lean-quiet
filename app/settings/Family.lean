import engine.core.Families
import engine.core.CodecVia
import app.settings.appearance.Op
import app.settings.appearance.Validate

/-
The settings family: this device's preferences, each a local op
(SETTINGS01, THEME01). Each op type is a folder below this one: its body
and fact (Op.lean) and its validator (Validate.lean). This file is the
registry: the sum of them (one so far, appearance), their bytes, which
validator judges which op, and the lists the family files facts in.

Every settings op is local and cites only settings facts, so the family
stands alone; the node's registry (app/Family.lean) puts it on top of
Community's and Connection's. Kinds 40–47.
-/

namespace Settings
open Engine Codec

/-- An op of the settings family: one op type's body. -/
inductive Body where
  | ofAppearance (b : Appearance.Body)

/-- A fact of the settings family: one op type's fact. -/
inductive Fact where
  | ofAppearance (f : Appearance.Fact)
  deriving Inhabited, BEq

/-- One op type so far: its body's and fact's bytes are the family's. -/
instance : Codec Body := Codec.via (fun | .ofAppearance b => b) .ofAppearance (fun | .ofAppearance _ => rfl)
instance : Codec Fact := Codec.via (fun | .ofAppearance f => f) .ofAppearance (fun | .ofAppearance _ => rfl)

/-- An op's kind, by its body. -/
def Body.kind : Body → UInt8
  | .ofAppearance _ => 40

@[simp] def Fact.appearance? : Fact → Option Appearance.Fact
  | .ofAppearance f => some f

/-- Where a fact sorts under its keys. -/
def sortOf : Fact → ByteArray
  | .ofAppearance f => Appearance.sortKey f

instance : SortKey Fact := ⟨sortOf⟩

/-- An op of this family, named by its bytes. -/
def mkOp (reqs : List Id) (b : Body) : Op := Op.make b.kind reqs (encode b)

/-- An op's validator, by its body: its op type's, given the facts it
cites. -/
def check (o : Op) : Body → List Fact → Option Fact
  | .ofAppearance b, [] => (Appearance.check o b).map .ofAppearance
  | _, _ => none

def validate (o : Op) (fs : List Fact) : Option Fact :=
  match (decode o.body : Option Body) with
  | some b => if b.kind = o.kind then check o b fs else none
  | none => none

/-! ## Relations: each op type's lists, read in the family (same names, so the same keys) -/

namespace appearance
def all : Rel Fact := Appearance.all.comap Fact.appearance?
end appearance

def rels : List (Rel Fact) := [appearance.all]

def keys : Fact → List ByteArray := keysOf rels

/-- Every settings op stays on this device. -/
def scopeOf (_ : Op) : Scope := .local

def owns (k : UInt8) : Bool := 40 ≤ k && k ≤ 47

end Settings
