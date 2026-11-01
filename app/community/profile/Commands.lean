import app.community.Family

/-!
`community.profile`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

def profile (c adm : Id) (by_ : Device) (name : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm]
  mkOp reqs (.profile name time (sig by_.sk reqs (.profile name time .empty)))

end Community
