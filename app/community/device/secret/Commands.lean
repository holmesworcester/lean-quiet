import app.community.Family

namespace Community
open Engine Codec

/-- This device's secret seed (local). -/
def secret (seed : ByteArray) : Op := mkOp [] (.secret (Device.ofSeed seed).pk seed)

end Community
