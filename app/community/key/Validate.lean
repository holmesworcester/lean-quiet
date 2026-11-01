import app.community.key.Op

namespace Community
open Engine Codec

namespace ContentKey

/-- Local: a 32-byte key, filed under its id. -/
def check : Body → Option Fact
  | ⟨c, k⟩ => if k.size = 32 then some ⟨c, kidOf cryptoSeal k, k⟩ else none

end ContentKey

end Community
