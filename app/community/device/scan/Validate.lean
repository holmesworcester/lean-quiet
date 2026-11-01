import app.community.device.scan.Op

namespace Community
open Engine Codec

namespace Scan

/-- Local: a bounded cursor and at most eight 32-byte node keys. -/
def check : Body → Option Fact
  | ⟨cursor, visited, time⟩ =>
    if cursor.size ≤ 256 ∧ visited.length ≤ 8 ∧ visited.all (·.size = 32) = true ∧ time < 2^64
    then some ⟨cursor, visited, time⟩ else none

end Scan

end Community
