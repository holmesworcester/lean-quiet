import app.connection.send.Op

namespace Connection
open Engine Codec

namespace Send

/-- It cites the op it carries. -/
def check (o : Op) : Body → Option Fact
  | ⟨addr⟩ => if 0 < addr.size then some ⟨o.reqs.headD .empty, addr⟩ else none

end Send

end Connection
