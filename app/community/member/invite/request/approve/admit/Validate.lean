import app.community.member.invite.request.approve.admit.Op
import app.community.member.invite.request.Op

namespace Community
open Engine Codec

namespace Admit

/-- It cites the community and the request; `tallied` says the rest of
what it cites are exactly the request's threshold of approvals of it, by
distinct users (the family reads them, `Community.tally`; issue #6 makes
them a typed dependency). -/
def check (o : Op) : Body → Root.Fact → Request.Fact → Bool → Option Fact
  | _, ⟨c, u0, _, _⟩, ⟨c1, u, d, e, _, _⟩, tallied =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ tallied = true
    then some ⟨c, u, d, e⟩ else none

end Admit

end Community
