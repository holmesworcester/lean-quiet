import app.community.key.Op

/-!
`community.key`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace ContentKey

/-- Local: a 32-byte key, filed under its id. -/
def check : Body → Option Fact
  | ⟨c, k⟩ => if k.size = 32 then some ⟨c, kidOf cryptoSeal k, k⟩ else none

end ContentKey

end Community
