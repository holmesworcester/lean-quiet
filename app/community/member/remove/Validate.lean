import app.community.member.remove.Op
import app.community.member.invite.request.approve.Op

namespace Community
open Engine Codec

namespace Remove

/-- The cut from the heads cited after the first four requirements: each
head's device, id and place in its chain, all of community c. -/
def cutOf (c : Id) : List Id → List Approve.Fact → Option (List (Key × Id × Nat))
  | [], [] => some []
  | x :: xs, h :: hs => if h.c = c then (cutOf c xs hs).map ((h.dev, x, h.n) :: ·) else none
  | _, _ => none

/-- It cites the community, its author's admission, its authority, and
an admission of the user it removes, then the approval chain heads it
keeps (its cut; none if one is not an approval). A self-removal needs
no admin, but its authority slot must be a shared fact (`shared`: a
shared op never reads this device's own state); otherwise the author
must be admin (`admin`, read by the family; issue #6). -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Bool → Bool → Root.Fact →
    Option (List Approve.Fact) → Option Fact
  | ⟨s⟩, ⟨c, u0, _, _, _⟩, ⟨c1, u, d, _, _⟩, shared, admin, ⟨c2, t, _, _, _⟩, heads =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ ((t = u ∧ shared = true) ∨ admin = true) ∧
      C.verify d (signedBy o (Body.unsigned ⟨s⟩)) s
    then (heads.bind (cutOf c (o.reqs.drop 4))).map fun k => ⟨c, t, u, k⟩ else none

end Remove

end Community
