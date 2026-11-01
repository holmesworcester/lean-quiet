import app.community.Family

namespace Community
open Engine Codec

/-- The admission of request req by these approvals. -/
def admit (c req : Id) (approvals : List Id := []) : Op := mkOp (c :: req :: approvals) .admit

end Community
