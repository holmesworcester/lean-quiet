import app.community.key.wrap.Op

namespace Community
open Engine Codec

namespace Wrap

/-- It cites the community, its author's admission and its recipient's,
and the author's device signs it. Its key id is the root's; its
recipient is the node key the recipient's admission names. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Root.Fact → Option Fact
  | ⟨bx, s⟩, ⟨c, u0, _, _, kid⟩, ⟨c1, _, d, _, _⟩, ⟨c2, _, _, e, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ C.verify d (signedBy o (Body.unsigned ⟨bx, s⟩)) s
    then some ⟨c, kid, e, bx⟩ else none

end Wrap

end Community
