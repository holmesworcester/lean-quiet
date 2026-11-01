import engine.wire.Noise
import engine.core.Engine
import ops.community.Op

/-
`recv` (local): the record of an op's arrival: when it arrived, and how,
on a connection or bare from an address. The node writes one for every
op it takes, so provenance is the node's own observation, never a
sender's claim (tiny's WireOrigin). It cites the op that arrived, and
only that.

Rules read it like any list. The responder answers to the address its
request arrived from (`conn.recv.byOp [r]`), and a screen can show when
a message arrived. Valid iff it cites one op.

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
ops/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Recv

/-- What its author writes. -/
structure Body where
  onConn : Bool
  via : B
  addr : B
  at_ : Nat
  deriving BEq

instance : Codec Body := Codec.tagged 38 (fun x => (x.onConn, x.via, x.addr, x.at_)) (fun (p : Bool × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 38 :: Codec.enc (x.onConn, x.via, x.addr, x.at_) := rfl

/-- Its fact, `recv`. -/
structure Fact where
  op : B
  onConn : Bool
  via : B
  addr : B
  at_ : Nat
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 6 (fun x => (x.op, x.onConn, x.via, x.addr, x.at_)) (fun (p : B × Bool × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 6 :: Codec.enc (x.op, x.onConn, x.via, x.addr, x.at_) := rfl

/-- Where its fact sorts: arrivals by time. -/
@[simp] def sortKey (f : Fact) : B := Community.be64 f.at_

/-! ## The lists its fact is filed in (`conn.recv.*`) -/
def byOp : Rel Fact := ⟨"conn.recv", "byOp", fun f => some [f.op]⟩
@[simp] theorem byOp_args (f : Fact) : byOp.args f = (some [f.op]) := rfl

end Recv

end Connection
