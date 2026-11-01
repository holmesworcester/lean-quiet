import app.community.member.join.joining.Op

namespace Community
open Engine Codec

namespace Joining

/-- Local: whatever this device records of its own join. -/
def check : Body → Option Fact
  | ⟨c, k, hs, r, nm, d, n⟩ => some ⟨c, k, hs, r, nm, d, n⟩

end Joining

end Community
