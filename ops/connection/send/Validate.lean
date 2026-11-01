import ops.connection.send.Op

/-!
`connection.send`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Connection
open Engine Codec

namespace Send

/-- It cites the op it carries. -/
def check (o : Op) : Body → Option Fact
  | ⟨addr⟩ => if 0 < addr.size then some ⟨o.reqs.headD .empty, addr⟩ else none

end Send

end Connection
