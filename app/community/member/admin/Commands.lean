import app.community.Family

namespace Community
open Engine Codec

def grant (c granterAdm auth targetAdm : Id) (by_ : Device) : Op :=
  let reqs := [c, granterAdm, auth, targetAdm]
  mkOp reqs (.grant (sig by_.sk reqs (.grant .empty)))

end Community
