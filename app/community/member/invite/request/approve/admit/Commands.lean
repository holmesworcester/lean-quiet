import app.community.Family

namespace Community
open Engine Codec

/-- The admission of request req by its approval `ok`. -/
def admit (c req ok : Id) : Op := mkOp [c, req, ok] .admit

end Community
