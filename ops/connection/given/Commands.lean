import engine.wire.Node
import ops.connection.Family
import engine.sync.Notice

/-!
`connection.given`: how it is written.
-/

namespace Connection
open Engine Codec

/-- The notice of removal x given on connection cid. -/
def Given.op (cid x : Id) : Op := mkOp [cid] (.given x)

end Connection

namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- Record a notice given on cid, so the rooms view stops carrying it. -/
def onGiven (cid x : Id) : List Op := [Given.op cid x]

end
end Connection
