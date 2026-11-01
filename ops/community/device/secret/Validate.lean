import ops.community.device.secret.Op

/-!
`community.device.secret`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Secret

/-- Local: the seed's key pair. -/
def check (C : Crypto) : Body → Option Fact
  | ⟨pk, seed⟩ => if C.pub seed = pk then some ⟨pk, seed⟩ else none

end Secret

end Community
