import app.community.Op

/-
An invitation, issued by an admitted device. A request it carries is
admitted by one approval (the user's call, 2026-10-31: no thresholds,
since one member can mint the distinct users any threshold would count).
A link invitation (another device for the issuer's user) is approved by
the issuer's user only.
-/

namespace Community
open Engine Codec

namespace Invitation

/-- What its author writes and signs. -/
structure Body where
  bearer : Key
  link : Bool
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 1 (fun x => (x.bearer, x.link, x.sig)) (fun (p : B × Bool × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 1 :: Codec.enc (x.bearer, x.link, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `invitation`. -/
structure Fact where
  c : Id
  issuer : Id
  bearer : Key
  link : Bool
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 1 (fun x => (x.c, x.issuer, x.bearer, x.link)) (fun (p : B × B × B × Bool) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 1 :: Codec.enc (x.c, x.issuer, x.bearer, x.link) := rfl

end Invitation

end Community
