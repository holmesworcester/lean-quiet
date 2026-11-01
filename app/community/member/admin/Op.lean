import app.community.Op

/-
An admin grants admin to another user. Admin cannot be revoked.
-/

namespace Community
open Engine Codec

namespace Grant

/-- What its author writes and signs. -/
structure Body where
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 3 (fun x => x.sig) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 3 :: Codec.enc x.sig := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `admin`. -/
structure Fact where
  c : Id
  u : Id
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 2 (fun x => (x.c, x.u)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 2 :: Codec.enc (x.c, x.u) := rfl

/-! ## The lists its fact is filed in (`admin.*`) -/
def byUser : Rel Fact := ⟨"admin", "byUser", fun f => some [f.c, f.u]⟩
@[simp] theorem byUser_args (f : Fact) : byUser.args f = (some [f.c, f.u]) := rfl

end Grant

end Community
