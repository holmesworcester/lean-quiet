/-
`recv` (local): the record of an op's arrival: when it arrived, and how,
on a connection or bare from an address. The node writes one for every
op it takes, so provenance is the node's own observation, never a
sender's claim (tiny's WireOrigin). It cites the op that arrived, and
only that.

Rules read it like any list. The responder answers to the address its
request arrived from (`conn.recv.byOp [r]`), and a screen can show when
a message arrived. Valid iff it cites one op.

**A connection over itself means "heard".** A `recv` that cites a
connection op and says it came on that very connection (`via` = the
connection's id) records not an arrival but that the session has heard
its peer: a round the peer answered under the session's keys ended one
of its rooms (`heardOp`, written by the node's settle hook). No op
arrives that way, since a connection op is conn-scope and never travels
on a session. The one-per-peer choice reads it (`heard`, `kept`), and a
close purges it with the connection. That it is written only after a
frame opened under the session's keys is `heard_stmt`.
-/
import ops.connection.Send

namespace Connection
open Engine

def Recv.check (o : Op) (onConn : Bool) (via addr : B) (at_ : Nat) : List F → Option Fact
  | [_] => some (.recv (o.reqs.headD .empty) onConn via addr at_)
  | _ => none

def Recv.op (x : Id) (via : Option Id) (addr : B) (at_ : Nat) : Op :=
  mkOp [x] (.recv via.isSome (via.getD .empty) addr at_)

namespace recv
def byOp : Rel Fact := ⟨"conn.recv", "byOp", fun | .recv x .. => some [x] | _ => none⟩
end recv

end Connection
