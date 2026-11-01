import ops.community.member.invite.Op

/-!
`community.member.invite`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Invitation

/-- It cites the community (its root's admission) and its author's
admission. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact
  | ⟨k, l, t, s⟩, ⟨c, u0, _, _⟩, ⟨c', u, d, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ 1 ≤ t ∧ (l = true → t = 1) ∧
      C.verify d (signedBy o (Body.unsigned ⟨k, l, t, s⟩)) s
    then some ⟨c, u, k, l, t⟩ else none

end Invitation

end Community
