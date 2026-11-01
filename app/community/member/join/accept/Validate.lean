import app.community.member.join.accept.Op

namespace Community
open Engine Codec

namespace Accept

/-- Local: this device records that it is in c. -/
def check : Body → Option Fact
  | ⟨c, d⟩ => some ⟨c, d⟩

end Accept

end Community
