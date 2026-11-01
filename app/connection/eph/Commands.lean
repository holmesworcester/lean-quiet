import engine.wire.Node
import app.connection.Family
import engine.sync.Notice

/-!
`connection.eph`: how it is written.
-/

namespace Connection
open Engine Codec

/-- Secret `sk`, drawn for handshake op `of`. -/
def Eph.op (sk : B) (of : Id) : Op := mkOp [of] (.eph sk)

end Connection

namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- The hello a request of this node's sealed (community, address, op
bytes), recovered from its own message 1 with its ephemeral (`sent1`,
as `established` does). -/
def helloOf (K : Keys) (sk : B) (r to m1 : B) : m (Option (B × B × List B)) := do
  match ← rows eph.byOf [r] with
  | (_, .eph _ _ e) :: _ =>
    return (Noise.sent1 K.suite prologue sk e to m1).bind fun (_, p1) =>
      (decode p1 : Option (B × B × List B))
  | _ => return none

end
end Connection
