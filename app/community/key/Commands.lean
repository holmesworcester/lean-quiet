import app.community.Family

namespace Community
open Engine Codec

/-- This device's copy of c's content key k (local). -/
def contentKey (c k : ByteArray) : Op := mkOp [] (.key c k)

end Community
