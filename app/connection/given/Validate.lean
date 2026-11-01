import app.connection.given.Op
import app.connection.connection.Op

namespace Connection
open Engine Codec

namespace Given

/-- It cites the connection it was given on. -/
def check (o : Op) : Body → Reply.Fact → Option Fact
  | ⟨x⟩, _ => some ⟨o.reqs.headD .empty, x⟩

end Given

end Connection
