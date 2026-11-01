import app.community.device.secret.Op

namespace Community
open Engine Codec

namespace Secret

/-- Local: the seed's key pair. -/
def check (C : Crypto) : Body → Option Fact
  | ⟨pk, seed⟩ => if C.pub seed = pk then some ⟨pk, seed⟩ else none

end Secret

end Community
