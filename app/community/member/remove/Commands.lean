import app.community.Family

namespace Community
open Engine

/-- The list of user u's removals in c, counted only. -/
def removals (c u : Id) : ListQ := removal.byUser.query [c, u] (limit := some 0)
open Engine Codec

/-- by_'s removal of a user, citing the community, its admission, its
authority, an admission of the target, and the approval chain heads it
keeps (`heads`: one per device of the target it holds, its cut). -/
def remove (c removerAdm auth targetAdm : Id) (by_ : Device) (heads : List Id := []) : Op :=
  let reqs := [c, removerAdm, auth, targetAdm] ++ heads
  mkOp reqs (.remove (sig by_.sk reqs (.remove .empty)))

end Community
