import app.community.device.endpoint.Op

namespace Community
open Engine Codec

namespace Endpoint

/-- Local: a 32-byte X25519 secret and its public key. -/
def check : Body → Option Fact
  | ⟨sk⟩ => if sk.size = 32 then some ⟨cryptoSeal.pub sk, sk⟩ else none

end Endpoint

end Community
