import ops.Commands
import engine.renderer.Row
import ops.community.Proofs

/-!
`community.channel.message`: its component, which reads its own facts, and the component's laws.
-/
namespace ViewLaws
open _root_.Engine _root_.Community _root_.Data

/-- The model: a list read is the engine's `eval` of a store. -/
abbrev Model := ReaderT (DB Fact) Id

instance : Reads Model where
  read q := fun db => match q with
    | .list q => .list (Engine.eval db q) []
    | .op _ => .bytes none

theorem pure_none_ne {α : Type} (db : DB Fact) (x : α) :
    (ReaderT.pure none : Model (Option α)) db ≠ some x := by intro h; cases h

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

/-- One fact, as the store holds it. -/
def factIn (db : DB Fact) (x : Id) : Option Fact :=
  (Engine.eval db { key := opKey x, limit := some 1 }).rows.head?.map (·.2)

end ViewLaws
