import engine.wire.Noise
import engine.core.Engine

/-
`connection` (conn scope): Noise message 2 (`e, ee, se`), the
responder's answer, as in poc-17's conn.connection. It cites the request
it answers. **Its op id is the connection id**: both ends hold the same
bytes, so both name the session the same way. The id depends on the
responder's fresh ephemeral, so nobody can name a session ahead of it.

Valid iff it cites a Valid request and holds an ephemeral key and a
tag. This is structural, like the request. Filed under
`conn.connection.byRequest [r]`.

`answer` writes the connection op, after `react` has applied the trust
rule. It writes an `eph`, the connection, this side's `established`, and
a courier carrying the connection's bytes back to the address the
request arrived from.

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
app/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Reply

/-- What its author writes. -/
structure Body where
  m2 : B
  deriving BEq

instance : Codec Body := Codec.tagged 35 (fun x => x.m2) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 35 :: Codec.enc x.m2 := rfl

/-- Its fact, `connection`. -/
structure Fact where
  req : B
  m2 : B
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 3 (fun x => (x.req, x.m2)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 3 :: Codec.enc (x.req, x.m2) := rfl

/-! ## The lists its fact is filed in (`conn.connection.*`) -/
def byRequest : Rel Fact := ⟨"conn.connection", "byRequest", fun f => some [f.req]⟩
@[simp] theorem byRequest_args (f : Fact) : byRequest.args f = (some [f.req]) := rfl

end Reply

end Connection
