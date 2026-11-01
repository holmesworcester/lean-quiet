import ops.community.Op

/-
The node's X25519 key: 32 random bytes, one per node. Local.

`community.device.endpoint`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Endpoint

/-- What its author writes. -/
structure Body where
  sk : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 22 (fun x => x.sk) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 22 :: Codec.enc x.sk := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `endpoint`. -/
structure Fact where
  pk : ByteArray
  sk : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 20 (fun x => (x.pk, x.sk)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 20 :: Codec.enc (x.pk, x.sk) := rfl

/-! ## The lists its fact is filed in (`endpoint.*`) -/
/-- This node's key (local): what it handshakes with, and what content
keys wrapped to its devices open with. -/
def all : Rel Fact := ⟨"endpoint", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Endpoint

end Community
