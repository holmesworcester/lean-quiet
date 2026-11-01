import ops.community.Op

/-
A device's signing key pair, from its 32-byte seed. Local.

`community.device.secret`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Secret

/-- What its author writes. -/
structure Body where
  pk : ByteArray
  seed : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 15 (fun x => (x.pk, x.seed)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 15 :: Codec.enc (x.pk, x.seed) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `secret`. -/
structure Fact where
  pk : ByteArray
  seed : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 11 (fun x => (x.pk, x.seed)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 11 :: Codec.enc (x.pk, x.seed) := rfl

/-! ## The lists its fact is filed in (`secret.*`) -/
/-- This device's own secret seeds, by public key: read by intents to
sign, never by views. -/
def byKey : Rel Fact := ⟨"secret", "byKey", fun f => some [f.pk]⟩
@[simp] theorem byKey_args (f : Fact) : byKey.args f = (some [f.pk]) := rfl
/-- Every device this node holds the secret of: the devices its network
node speaks for. -/
def all : Rel Fact := ⟨"secret", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Secret

end Community
