import app.community.Family

namespace Community
open Engine Codec

/-- This device is in community c (local). -/
def accept (c : Id) (device : Key) : Op := mkOp [] (.accept c device)

end Community
