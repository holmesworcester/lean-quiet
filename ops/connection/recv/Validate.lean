import ops.connection.recv.Op

/-!
`connection.recv`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Connection
open Engine Codec

namespace Recv

/-- It cites the op that arrived. -/
def check (o : Op) : Body → Option Fact
  | ⟨onConn, via, addr, at_⟩ => some ⟨o.reqs.headD .empty, onConn, via, addr, at_⟩

end Recv

end Connection
