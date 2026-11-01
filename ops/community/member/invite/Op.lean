import ops.community.Op

/-
An invitation, issued by an admitted device, with how many approvals a
request it carries needs: at least one. A link invitation (another device
for the issuer's user) needs exactly one, by the issuer's user.

`community.member.invite`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Invitation

/-- What its author writes and signs. -/
structure Body where
  bearer : Key
  link : Bool
  threshold : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 1 (fun x => (x.bearer, x.link, x.threshold, x.sig)) (fun (p : B × Bool × Nat × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 1 :: Codec.enc (x.bearer, x.link, x.threshold, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `invitation`. -/
structure Fact where
  c : Id
  issuer : Id
  bearer : Key
  link : Bool
  threshold : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 1 (fun x => (x.c, x.issuer, x.bearer, x.link, x.threshold)) (fun (p : B × B × B × Bool × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 1 :: Codec.enc (x.c, x.issuer, x.bearer, x.link, x.threshold) := rfl

end Invitation

end Community
