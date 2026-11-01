import ops.community.member.invite.request.Op
import ops.community.member.invite.Op

/-!
`community.member.invite.request`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Request

/-- It cites the community and the invitation it redeems: signed by the
requesting device and by the invitation's bearer key. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Invitation.Fact → Option Fact
  | ⟨d, e, cs, bs⟩, ⟨c, u0, _, _⟩, ⟨c', issuer, k, l, t⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ C.verify d (signedBy o (Body.unsigned ⟨d, e, cs, bs⟩)) cs ∧
      C.verify k (signedBy o (Body.unsigned ⟨d, e, cs, bs⟩)) bs
    then some ⟨c, if l then issuer else o.id, d, e, l, t⟩ else none

end Request

end Community
