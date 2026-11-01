import ops.community.member.remove.Op

/-!
`community.member.remove`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Remove

/-- It cites the community, its author's admission, its authority, and
an admission of the user it removes. A self-removal needs no admin, but
its authority slot must be a shared fact (`shared`: a shared op never
reads this device's own state); otherwise the author must be admin
(`admin`, read by the family; issue #6). -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Bool → Bool → Root.Fact → Option Fact
  | ⟨s⟩, ⟨c, u0, _, _⟩, ⟨c1, u, d, _⟩, shared, admin, ⟨c2, t, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ ((t = u ∧ shared = true) ∨ admin = true) ∧
      C.verify d (signedBy o (Body.unsigned ⟨s⟩)) s
    then some ⟨c, t, u⟩ else none

end Remove

end Community
