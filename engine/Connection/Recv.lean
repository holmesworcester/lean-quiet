/-
`recv` (local): the record of an op's arrival: when it arrived, and how,
on a connection or bare from an address. The node writes one for every
op it takes, so provenance is a node observation, never a sender's
claim (tiny's WireOrigin). It cites the op that arrived, and only that:
it outlives the session, so it does not cite the connection.

Rules read it like any list: `answer` sends back to the address a
request arrived from (`recv.byOp [r]`); a screen can show when a
message arrived. Valid iff it cites one op.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Send

namespace Connection
open Engine Engine.Sync

structure Recv where
  via : Option Id
  addr : ByteArray
  at_ : Nat

def Recv.kind : UInt8 := 38

def Recv.op (o : Id) (via : Option Id) (addr : ByteArray) (at_ : Nat) : Op := sorry

end Connection
