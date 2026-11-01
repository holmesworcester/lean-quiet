import ops.community.device.endpoint.Op

/-!
`community.device.endpoint`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Endpoint

/-- Local: a 32-byte X25519 secret and its public key. -/
def check : Body → Option Fact
  | ⟨sk⟩ => if sk.size = 32 then some ⟨cryptoSeal.pub sk, sk⟩ else none

end Endpoint

end Community
