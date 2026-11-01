import ops.community.Family

/-!
`community.device.secret`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- This device's secret seed (local). -/
def secret (seed : ByteArray) : Op := mkOp [] (.secret (Device.ofSeed seed).pk seed)

end Community
