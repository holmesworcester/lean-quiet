import engine.wire.Noise
import engine.core.Engine

/-
`send` (local): a courier, the one way out for the two handshake
messages (tiny's and poc-17's egress door). It cites the op it carries
and names the bare address it goes to. Session traffic needs no courier:
the node seals it into frames. Commands write couriers; they never send
anything themselves.

The node lists `conn.send.all` and reads each carried op's bytes when it
hands the courier out (poc-17's `ship`, by reference). It then purges
the courier. Purging a session purges its couriers with it, because they
cite its ops. A courier is content-addressed, so writing the same send
again is one op until the first is purged. Valid iff the carried op is
and the address is non-empty.

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
ops/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Send

/-- What its author writes. -/
structure Body where
  addr : B
  deriving BEq

instance : Codec Body := Codec.tagged 37 (fun x => x.addr) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 37 :: Codec.enc x.addr := rfl

/-- Its fact, `send`. -/
structure Fact where
  op : B
  addr : B
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 5 (fun x => (x.op, x.addr)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 5 :: Codec.enc (x.op, x.addr) := rfl

/-! ## The lists its fact is filed in (`conn.send.*`) -/
def all : Rel Fact := ⟨"conn.send", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Send

end Connection
