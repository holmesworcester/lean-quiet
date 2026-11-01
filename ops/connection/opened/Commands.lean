import engine.wire.Node
import ops.connection.Family
import engine.sync.Notice

/-!
`connection.opened`: how it is written.
-/

namespace Connection
open Engine Codec

/-- Open request `req` with this node's endpoint op `epOp`. -/
def Opened.op (req epOp : Id) : Op := mkOp [req, epOp] .opened

end Connection

namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- open: an `opened`, citing this node's endpoint op, for each of these
requests to its key not opened yet. -/
def openEach (epOp : Id) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (r, _) :: t => do
    let n ← count opened.byRequest [r]
    let rest ← openEach epOp t
    return if n = 0 then Opened.op r epOp :: rest else rest

end
end Connection
