import ops.connection.Family

/-!
`connection.send`: how it is written.
-/

namespace Connection
open Engine Codec

/-- A courier carrying op x to a bare address. -/
def Send.op (addr : B) (x : Op) : Op := mkOp [x.id] (.send addr)

end Connection
