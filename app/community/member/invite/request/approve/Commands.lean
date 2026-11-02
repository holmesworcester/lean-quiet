import app.community.Family

namespace Community
open Engine Codec

/-- by_'s approval of request req, signed as its admission adm, citing
the approval that admitted by_ (`up`, none for the founder's device) and
by_'s previous approval (`prev`, none for its first). -/
def approve (c req adm : Id) (by_ : Device) (up prev : Option Id := none) : Op :=
  let reqs := [c, req, adm] ++ up.toList ++ prev.toList
  mkOp reqs (.approve (sig by_.sk reqs (.approve .empty)))

end Community
