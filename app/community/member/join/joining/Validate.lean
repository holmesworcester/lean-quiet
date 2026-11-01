import app.community.member.join.joining.Op

/-!
`community.member.join.joining`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Joining

/-- Local: whatever this device records of its own join. -/
def check : Body → Option Fact
  | ⟨c, k, hs, r, nm, d, n⟩ => some ⟨c, k, hs, r, nm, d, n⟩

end Joining

end Community
