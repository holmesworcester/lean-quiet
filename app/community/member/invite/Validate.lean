import app.community.member.invite.Op

namespace Community
open Engine Codec

namespace Invitation

/-- It cites the community (its root's admission) and its author's
admission. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact
  | ⟨k, l, s⟩, ⟨c, u0, _, _⟩, ⟨c', u, d, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ C.verify d (signedBy o (Body.unsigned ⟨k, l, s⟩)) s
    then some ⟨c, u, k, l⟩ else none

end Invitation

end Community
