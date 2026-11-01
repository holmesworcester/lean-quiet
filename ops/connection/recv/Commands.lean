import ops.connection.Family

/-!
`connection.recv`: how it is written.
-/

namespace Connection
open Engine Codec

def Recv.op (x : Id) (via : Option Id) (addr : B) (at_ : Nat) : Op :=
  mkOp [x] (.recv via.isSome (via.getD .empty) addr at_)

end Connection
