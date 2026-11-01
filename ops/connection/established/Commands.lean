import ops.connection.Family

/-!
`connection.established`: how it is written.
-/

namespace Connection
open Engine Codec

def Established.op (cid req eph epOp : Id) : Op := mkOp [cid, req, eph, epOp] .established

end Connection
