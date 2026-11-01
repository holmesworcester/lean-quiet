import engine.core.Families
import app.nav.Op
import app.nav.Validate

/-
The nav family: one op, this window's place (app/nav). This file is the
registry: its bytes, its validator and its list, and where it lives: in
the app's ephemeral log only (`scopeOf`), so the engine never stores it
in SQLite (`Engine.intake_durable`) and sync never offers it. The node's
registry (app/Family.lean) puts it on top with the settings. Kinds 48–55.
-/

namespace Nav
open Engine Codec

/-- An op's kind, by its body. -/
def Body.kind (_ : Body) : UInt8 := 48

instance : SortKey Fact := ⟨sortKey⟩

/-- An op of this family, named by its bytes. -/
def mkOp (reqs : List Id) (b : Body) : Op := Op.make b.kind reqs (encode b)

def validate (o : Op) (fs : List Fact) : Option Fact :=
  match (decode o.body : Option Body), fs with
  | some b, [] => if b.kind = o.kind then check o b else none
  | _, _ => none

def rels : List (Rel Fact) := [all]

def keys : Fact → List ByteArray := keysOf rels

/-- Every nav op lives only in memory. -/
def scopeOf (_ : Op) : Scope := .ephemeral

def owns (k : UInt8) : Bool := 48 ≤ k && k ≤ 55

end Nav
