import app.connection.recv.Op

namespace Connection
open Engine Codec

namespace Recv

/-- It cites the op that arrived. -/
def check (o : Op) : Body → Option Fact
  | ⟨onConn, via, addr, at_⟩ => some ⟨o.reqs.headD .empty, onConn, via, addr, at_⟩

end Recv

end Connection
