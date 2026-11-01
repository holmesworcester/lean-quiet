import app.community.member.invite.request.approve.Op
import app.community.member.invite.request.Op

namespace Community
open Engine Codec

namespace Approve

/-- It cites the community, the request it approves, and its author's
admission, by another device than the requester's. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Request.Fact → Root.Fact → Option Fact
  | ⟨s⟩, ⟨c, u0, _, _⟩, ⟨c1, u, d, _, l⟩, ⟨c2, a, da, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ (l = true → a = u) ∧ da ≠ d ∧
      C.verify da (signedBy o (Body.unsigned ⟨s⟩)) s
    then some ⟨c, o.reqs.getD 1 .empty, a⟩ else none

end Approve

end Community
