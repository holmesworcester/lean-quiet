/-
`opened` (local, the responder's): a request it has read. It cites the
request and this node's `endpoint` op (Community's). Its validator runs
Noise's `read1` with the endpoint's secret as this side's static and the
request's sender key as the initiator's. It is Valid iff the request is
to this node's key and opens, and its hello decodes. Its
fact is the request, the community, the initiator, the address the
initiator listens on, and the ops the hello delivers.

This is poc-17's `Keys`: a local op cites the secret, so the shared op
needs no secret to be judged. Filed under `conn.opened.all` and
`conn.opened.byRequest [r]`. A close purges it with the request.
-/
import ops.connection.Request

namespace Connection
open Engine Codec

def Opened.check (K : Keys) (o : Op) : List F → Option Fact
  | [.inr (.request to frm m1), .inl (.endpoint pk sk)] =>
    if pk ≠ to then none else
    match Noise.read1 K.suite prologue sk frm m1 with
    | some (_, _, p) =>
      match (decode p : Option (B × B × List B)) with
      | some (c, addr, ops) => some (.opened (o.reqs.headD .empty) c frm addr ops)
      | none => none
    | none => none
  | _ => none

/-- Open request `req` with this node's endpoint op `epOp`. -/
def Opened.op (req epOp : Id) : Op := mkOp [req, epOp] .opened

namespace opened
def all : Rel Fact := ⟨"conn.opened", "all", fun | .opened .. => some [] | _ => none⟩
def byRequest : Rel Fact := ⟨"conn.opened", "byRequest", fun | .opened r .. => some [r] | _ => none⟩
end opened

end Connection
