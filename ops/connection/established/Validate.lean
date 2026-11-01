import ops.connection.established.Op
import ops.connection.connection.Op
import ops.connection.request.Op
import ops.connection.eph.Op
import ops.community.device.endpoint.Op

/-!
`connection.established`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Connection
open Engine Codec

namespace Established

/-- It cites the connection, the request, its own ephemeral secret and this node's key. -/
def check (K : Keys) (o : Op) : Body → Reply.Fact → Request.Fact → Eph.Fact → Community.Endpoint.Fact → Option Fact
  | _, ⟨r, m2⟩, ⟨to, frm, m1⟩, ⟨_, _, esk⟩, ⟨pk, sk⟩ =>
    let cid := o.reqs.headD .empty
    if o.reqs.getD 1 .empty ≠ r then none
    else if pk = to then do
      -- the responder
      let (st, re, p1) ← Noise.read1 K.suite prologue sk frm m1
      let (c, _, _) ← (decode p1 : Option (B × B × List B))
      let (sr, m2') ← Noise.write2 K.suite st esk frm re .empty
      if m2' ≠ m2 then none
      else some ⟨cid, c, frm, sr.h, sr.send.k, sr.recv.k, false⟩
    else if pk = frm then do
      -- the initiator
      let (st, p1) ← Noise.sent1 K.suite prologue sk esk to m1
      let (c, _, _) ← (decode p1 : Option (B × B × List B))
      let (si, _) ← Noise.read2 K.suite st sk esk m2
      some ⟨cid, c, to, si.h, si.send.k, si.recv.k, true⟩
    else none

end Established

end Connection
