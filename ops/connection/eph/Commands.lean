import ops.connection.Family

/-!
`connection.eph`: how it is written.
-/

namespace Connection
open Engine Codec

/-- Secret `sk`, drawn for handshake op `of`. -/
def Eph.op (sk : B) (of : Id) : Op := mkOp [of] (.eph sk)

end Connection
