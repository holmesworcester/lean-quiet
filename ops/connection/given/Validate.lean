import ops.connection.given.Op
import ops.connection.connection.Op

/-!
`connection.given`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Connection
open Engine Codec

namespace Given

/-- It cites the connection it was given on. -/
def check (o : Op) : Body → Reply.Fact → Option Fact
  | ⟨x⟩, _ => some ⟨o.reqs.headD .empty, x⟩

end Given

end Connection
