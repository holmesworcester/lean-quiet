import app.community.device.scan.Op

namespace Community
open Engine Codec

namespace Scan

/-- Local: a bounded cursor. -/
def check : Body → Option Fact
  | ⟨cursor, time⟩ => if cursor.size ≤ 256 ∧ time < 2^64 then some ⟨cursor, time⟩ else none

end Scan

end Community
