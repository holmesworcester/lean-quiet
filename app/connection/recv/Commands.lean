import engine.wire.Node
import app.connection.Family
import engine.sync.Notice

/-!
`connection.recv`: how it is written.
-/

namespace Connection
open Engine Codec

def Recv.op (x : Id) (via : Option Id) (addr : B) (at_ : Nat) : Op :=
  mkOp [x] (.recv via.isSome (via.getD .empty) addr at_)

end Connection

namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- The bare address op x arrived from, if it arrived bare. -/
def arrivedFrom (x : Id) : m (Option B) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a _ => some a
    | _ => none

/-- When and from where op x first arrived bare, if it did. -/
def arrival (x : Id) : m (Option (B × Nat)) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a t => some (a, t)
    | _ => none

end
end Connection
