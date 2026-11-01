import app.community.Family

namespace Community
open Engine Codec

def profile (c adm : Id) (by_ : Device) (name : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm]
  mkOp reqs (.profile name time (sig by_.sk reqs (.profile name time .empty)))

end Community
