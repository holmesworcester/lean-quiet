import app.community.device.retry.Op

namespace Community
open Engine Codec

namespace Retry

/-- Local: a 32-byte node key and two 64-bit counters. -/
def check : Body → Option Fact
  | ⟨peer, time, attempts⟩ =>
    if peer.size = 32 ∧ time < 2^64 ∧ attempts < 2^64 then some ⟨peer, time, attempts⟩ else none

end Retry

end Community
