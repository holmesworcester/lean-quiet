import app.community.member.admin.Op

namespace Community
open Engine Codec

namespace Grant

/-- It cites the community, its author's admission, what makes the
author admin (`admin`, read by the family: `Community.isAdmin`; issue
#6 makes it the author's grant, a typed dependency), and the admission
of the user it makes admin. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Bool → Root.Fact → Option Fact
  | ⟨s⟩, ⟨c, u0, _, _, _⟩, ⟨c1, u, d, _, _⟩, admin, ⟨c2, t, _, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ admin = true ∧
      C.verify d (signedBy o (Body.unsigned ⟨s⟩)) s
    then some ⟨c, t⟩ else none

end Grant

end Community
