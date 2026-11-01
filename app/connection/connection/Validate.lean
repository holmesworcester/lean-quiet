import app.connection.connection.Op
import app.connection.request.Op

namespace Connection
open Engine Codec

namespace Reply

/-- It cites the request it answers. -/
def check (o : Op) : Body → Request.Fact → Option Fact
  | ⟨m2⟩, _ => if 48 ≤ m2.size then some ⟨o.reqs.headD .empty, m2⟩ else none

end Reply

end Connection
