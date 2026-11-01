import app.community.member.invite.request.approve.admit.Op
import app.community.member.invite.request.Op
import app.community.member.invite.request.approve.Op

namespace Community
open Engine Codec

namespace Admit

/-- It cites the community, the request, and exactly one approval of
that request (the approval names the request it cites). -/
def check (o : Op) : Body → Root.Fact → Request.Fact → Approve.Fact → Option Fact
  | _, ⟨c, u0, _, _⟩, ⟨c1, u, d, e, _⟩, a =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ a.c = c ∧ a.req = o.reqs.getD 1 .empty
    then some ⟨c, u, d, e⟩ else none

end Admit

end Community
