import ops.community.Op

/-
This node's copy of a community's content key. Local.

`community.key`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace ContentKey

/-- What its author writes. -/
structure Body where
  c : ByteArray
  k : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 18 (fun x => (x.c, x.k)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 18 :: Codec.enc (x.c, x.k) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `key`. -/
structure Fact where
  c : ByteArray
  kid : ByteArray
  k : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 16 (fun x => (x.c, x.kid, x.k)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 16 :: Codec.enc (x.c, x.kid, x.k) := rfl

/-! ## The lists its fact is filed in (`key.*`) -/
/-- This device's content keys for c (local). -/
def byCommunity : Rel Fact := ⟨"key", "byCommunity", fun f => some [f.c]⟩
@[simp] theorem byCommunity_args (f : Fact) : byCommunity.args f = (some [f.c]) := rfl
/-- This device's content key by id (local). -/
def byId : Rel Fact := ⟨"key", "byId", fun f => some [f.kid]⟩
@[simp] theorem byId_args (f : Fact) : byId.args f = (some [f.kid]) := rfl

end ContentKey

end Community
