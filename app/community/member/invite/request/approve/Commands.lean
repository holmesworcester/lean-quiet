import app.community.Family

namespace Community
open Engine Codec

/-- by_'s approval of request req, signed as its admission adm. -/
def approve (c req adm : Id) (by_ : Device) : Op :=
  let reqs := [c, req, adm]
  mkOp reqs (.approve (sig by_.sk reqs (.approve .empty)))

end Community
