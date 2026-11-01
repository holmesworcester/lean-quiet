import ops.community.Op

/-
This device is in a community, joined or waiting. Local.

`community.member.join.accept`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Accept

/-- What its author writes. -/
structure Body where
  c : Id
  device : Key
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 13 (fun x => (x.c, x.device)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 13 :: Codec.enc (x.c, x.device) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `accepted`. -/
structure Fact where
  c : Id
  device : Key
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 12 (fun x => (x.c, x.device)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 12 :: Codec.enc (x.c, x.device) := rfl

/-! ## The lists its fact is filed in (`accepted.*`) -/
/-- The communities this device is in, joined or waiting. -/
def all : Rel Fact := ⟨"accepted", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Accept

end Community
