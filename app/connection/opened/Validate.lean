import app.connection.opened.Op
import app.connection.request.Op
import app.community.device.endpoint.Op

namespace Connection
open Engine Codec

namespace Opened

/-- It cites the request it read and this node's key. -/
def check (K : Keys) (o : Op) : Body → Request.Fact → Community.Endpoint.Fact → Option Fact
  | _, ⟨to, frm, m1⟩, ⟨pk, sk⟩ =>
    if pk ≠ to then none else
    match Noise.read1 K.suite prologue sk frm m1 with
    | some (_, _, p) =>
      match (decode p : Option (B × B × List B)) with
      | some (c, addr, ops) => some ⟨o.reqs.headD .empty, c, frm, addr, ops⟩
      | none => none
    | none => none

end Opened

end Connection
