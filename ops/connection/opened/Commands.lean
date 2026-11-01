import ops.connection.Family

/-!
`connection.opened`: how it is written.
-/

namespace Connection
open Engine Codec

/-- Open request `req` with this node's endpoint op `epOp`. -/
def Opened.op (req epOp : Id) : Op := mkOp [req, epOp] .opened

end Connection
