import engine.renderer.Data
import engine.renderer.Row
import ops.community.Proofs

/-!
`community.key`: its component, which reads its own facts, and the component's laws.
-/
namespace ViewLaws
open _root_.Engine _root_.Community _root_.Data

/-- The first row of key.byId [kid], as the store holds it. -/
def keyIn (db : DB Fact) (kid : ByteArray) : Option Fact :=
  (Engine.eval db (key.byId.query [kid] (limit := some 1))).rows.head?.map (·.2)

end ViewLaws
