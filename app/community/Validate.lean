import app.community.Op

/-!
`community`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Root

/-- A root founds a community: signed by the founding device, it
admits the founder, whose user is the community. -/
def check (C : Crypto) (o : Op) : Body → Option Fact
  | ⟨d, e, s⟩ =>
    if C.verify d (signedBy o (Body.unsigned ⟨d, e, s⟩)) s then some ⟨o.id, o.id, d, e⟩ else none

end Root

end Community
