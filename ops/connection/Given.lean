/-
`given` (local): the notice of removal x was given on connection cid
(docs/REMOVAL.md). When a node decides a removal, each session with the
removed member's node carries a notice (`roomsV`): the removal and its
requirement closure, given once (`Conn.give`); the node then writes this
op. It cites the connection, so closing the session purges it.

Why it is an op: the rooms view reads it. A notice given on a session
is not carried again, so the session then carries nothing and is closed
(`notice_then_cut`). Without it, the view would carry the notice for as
long as the session lives: the session would never close, and a session
reopened from its ops (a restart) would give the notice again, as would
a connection's memory, which dies with it.

Valid iff it cites a connection. Filed under `conn.given.byConn [cid]`.
-/
import ops.connection.Recv

namespace Connection
open Engine

def Given.check (o : Op) (x : B) : List F → Option Fact
  | [.inr (.connection ..)] => some (.given (o.reqs.headD .empty) x)
  | _ => none

/-- The notice of removal x given on connection cid. -/
def Given.op (cid x : Id) : Op := mkOp [cid] (.given x)

namespace given
def byConn : Rel Fact := ⟨"conn.given", "byConn", fun | .given c _ => some [c] | _ => none⟩
end given

end Connection
