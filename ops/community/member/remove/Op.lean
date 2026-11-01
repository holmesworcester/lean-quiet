import ops.community.Op

/-
A removal names a user. It is Valid when its author's user is an admin,
or removes itself. Removal never invalidates an op; it changes who counts
as a member (docs/REMOVAL.md).

`community.member.remove`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Remove

/-- What its author writes and signs. -/
structure Body where
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 4 (fun x => x.sig) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 4 :: Codec.enc x.sig := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `removal`. -/
structure Fact where
  c : Id
  u : Id
  by_ : Id
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 3 (fun x => (x.c, x.u, x.by_)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 3 :: Codec.enc (x.c, x.u, x.by_) := rfl

/-! ## The lists its fact is filed in (`removal.*`) -/
def byUser : Rel Fact := ⟨"removal", "byUser", fun f => some [f.c, f.u]⟩
@[simp] theorem byUser_args (f : Fact) : byUser.args f = (some [f.c, f.u]) := rfl

end Remove

end Community
