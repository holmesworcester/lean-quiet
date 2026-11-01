import ops.connection.eph.Op

/-!
`connection.eph`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Connection
open Engine Codec

namespace Eph

/-- It cites the handshake op it was drawn for. -/
def check (K : Keys) (o : Op) : Body → Option Fact
  | ⟨sk⟩ => if sk.size = 32 then some ⟨o.reqs.headD .empty, K.suite.pub sk, sk⟩ else none

end Eph

end Connection
