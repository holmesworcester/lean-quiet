import app.community.Op

namespace Community
open Engine Codec

namespace Root

/-- A root founds a community: signed by the founding device, it
admits the founder, whose user is the community, and names the
community's content key id. -/
def check (C : Crypto) (o : Op) : Body → Option Fact
  | ⟨d, e, k, s⟩ =>
    if C.verify d (signedBy o (Body.unsigned ⟨d, e, k, s⟩)) s then some ⟨o.id, o.id, d, e, k⟩ else none

end Root

end Community
