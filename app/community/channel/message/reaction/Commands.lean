import app.community.Family

namespace Community
open Engine Codec

def react (c adm target : Id) (by_ : Device) (emoji : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm, target]
  mkOp reqs (.react emoji time (sig by_.sk reqs (.react emoji time .empty)))
open Engine

/-- React to a message as device d. -/
def reactTo (c myAdm target : Id) (d : Device) (emoji : ByteArray) (time : Nat) : Write :=
  ⟨[react c myAdm target d emoji time]⟩

end Community
