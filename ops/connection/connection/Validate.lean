import ops.connection.connection.Op
import ops.connection.request.Op

/-!
`connection.connection`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Connection
open Engine Codec

namespace Reply

/-- It cites the request it answers. -/
def check (o : Op) : Body → Request.Fact → Option Fact
  | ⟨m2⟩, _ => if 48 ≤ m2.size then some ⟨o.reqs.headD .empty, m2⟩ else none

end Reply

end Connection
