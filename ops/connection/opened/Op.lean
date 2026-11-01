import engine.wire.Noise
import engine.core.Engine

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

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
ops/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Opened

/-- What its author writes. -/
structure Body where
  deriving BEq

instance : Codec Body := Codec.tagged 34 (fun _ => ()) (fun _ => {}) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = [34] := rfl

/-- Its fact, `opened`. -/
structure Fact where
  req : B
  c : B
  frm : B
  addr : B
  ops : List B
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 2 (fun x => (x.req, x.c, x.frm, x.addr, x.ops)) (fun (p : B × B × B × B × List B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 2 :: Codec.enc (x.req, x.c, x.frm, x.addr, x.ops) := rfl

/-! ## The lists its fact is filed in (`conn.opened.*`) -/
def all : Rel Fact := ⟨"conn.opened", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl
def byRequest : Rel Fact := ⟨"conn.opened", "byRequest", fun f => some [f.req]⟩
@[simp] theorem byRequest_args (f : Fact) : byRequest.args f = (some [f.req]) := rfl

end Opened

end Connection
