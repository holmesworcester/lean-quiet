import app.community.profile.Op

namespace Community
open Engine Codec

namespace Profile

/-- It cites the community and its author's admission. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact
  | ⟨n, tm, s⟩, ⟨c, u0, _, _, _⟩, ⟨c1, u, d, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ n.size ≤ 64 ∧ C.verify d (signedBy o (Body.unsigned ⟨n, tm, s⟩)) s
    then some ⟨c, u, n, tm⟩ else none

end Profile

end Community
