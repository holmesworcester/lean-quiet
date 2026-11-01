import app.community.Family

namespace Community
open Engine

/-- The list of user u's removals in c, counted only. -/
def removals (c u : Id) : ListQ := removal.byUser.query [c, u] (limit := some 0)
open Engine Codec

def remove (c removerAdm auth targetAdm : Id) (by_ : Device) : Op :=
  let reqs := [c, removerAdm, auth, targetAdm]
  mkOp reqs (.remove (sig by_.sk reqs (.remove .empty)))

end Community
