import ops.community.member.join.accept.Op

/-!
`community.member.join.accept`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Accept

/-- Local: this device records that it is in c. -/
def check : Body → Option Fact
  | ⟨c, d⟩ => some ⟨c, d⟩

end Accept

end Community
