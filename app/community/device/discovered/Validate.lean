import app.community.device.discovered.Op

namespace Community
open Engine Codec

namespace Discovered

/-- Local: a 32-byte node key, at most eight valid hints, a TTL of at
most `Hints.maxAge`. -/
def check : Body → Option Fact
  | ⟨peer, hints, time, ttl⟩ =>
    if peer.size = 32 ∧ Hints.valid hints = true ∧ ttl ≤ Hints.maxAge ∧ time < 2^64
    then some ⟨peer, hints, time, ttl⟩ else none

end Discovered

end Community
