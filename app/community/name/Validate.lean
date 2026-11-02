import app.community.name.Op

namespace Community
open Engine Codec

namespace Rename

/-- It cites the community, its author's admission, what makes the author
admin (`admin`, read by the family; issue #6), and the names before it:
`counted` says its counter is one more than the highest of them (the
family reads them, `Community.counterOk`). -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Bool → Bool → Option Fact
  | ⟨n, nm, s⟩, ⟨c, u0, _, _, _⟩, ⟨c1, u, d, _, _⟩, admin, counted =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ admin = true ∧ nm.size ≤ 64 ∧ counted = true ∧
      C.verify d (signedBy o (Body.unsigned ⟨n, nm, s⟩)) s
    then some ⟨c, u, nm, n⟩ else none

end Rename

end Community
