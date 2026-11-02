import app.community.Family

namespace Community
open Engine

/-- A notice: payload `box` sealed to `recipient`, revision `time`,
signed by device `by_` admitted as `adm` in c. -/
def notice (c adm : Id) (by_ : Device) (recipient box : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm]
  mkOp reqs (.notice recipient box time (sig by_.sk reqs (.notice recipient box time .empty)))

end Community
