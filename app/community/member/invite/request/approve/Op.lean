import app.community.Op

/-
A member's signed yes to a request, by another device than the
requester's; a link request is approved by the issuer's user only. It
cites the request, so approvals come after it.

`community.member.invite.request.approve`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is app/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Approve

/-- What its author writes and signs. -/
structure Body where
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 10 (fun x => x.sig) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 10 :: Codec.enc x.sig := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `approval`. -/
structure Fact where
  c : Id
  req : Id
  u : Id
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 10 (fun x => (x.c, x.req, x.u)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 10 :: Codec.enc (x.c, x.req, x.u) := rfl

/-! ## The lists its fact is filed in (`approval.*`) -/
def byRequest : Rel Fact := ⟨"approval", "byRequest", fun f => some [f.c, f.req]⟩
@[simp] theorem byRequest_args (f : Fact) : byRequest.args f = (some [f.c, f.req]) := rfl

end Approve

end Community
