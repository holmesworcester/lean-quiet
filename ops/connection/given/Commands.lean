import ops.connection.Family

/-!
`connection.given`: how it is written.
-/

namespace Connection
open Engine Codec

/-- The notice of removal x given on connection cid. -/
def Given.op (cid x : Id) : Op := mkOp [cid] (.given x)

end Connection
