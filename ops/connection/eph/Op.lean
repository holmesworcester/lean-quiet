import engine.wire.Noise
import engine.core.Engine

/-
`eph` (local): one ephemeral X25519 secret for one handshake, drawn at
random from the OS by the side that uses it: the initiator's `e`, the
responder's `f`. It cites the handshake op it was drawn for (the
request, or the connection), so purging the session purges it with no
search. The side's `established` op cites it. That is what leaves the
session's traffic unreadable afterwards: the transport keys depend on
`ee`, and no other copy of either secret exists.

Valid iff the secret is 32 bytes. Its fact is that op, the public key
and the secret, filed under `conn.eph.byOf [op]`.

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
ops/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Eph

/-- What its author writes. -/
structure Body where
  sk : B
  deriving BEq

instance : Codec Body := Codec.tagged 32 (fun x => x.sk) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 32 :: Codec.enc x.sk := rfl

/-- Its fact, `eph`. -/
structure Fact where
  of : B
  pk : B
  sk : B
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 0 (fun x => (x.of, x.pk, x.sk)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 0 :: Codec.enc (x.of, x.pk, x.sk) := rfl

/-! ## The lists its fact is filed in (`conn.eph.*`) -/
def byOf : Rel Fact := ⟨"conn.eph", "byOf", fun f => some [f.of]⟩
@[simp] theorem byOf_args (f : Fact) : byOf.args f = (some [f.of]) := rfl

end Eph

end Connection
