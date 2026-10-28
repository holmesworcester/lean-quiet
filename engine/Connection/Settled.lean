/-
`settled` (local): room r of connection cid is settled here. Sync
reports a synced room settled once its first round has ended with
nothing wanted outstanding, and a notice once it has been given
(`Conn.give`); the node writes this op for each (`Hooks.settled`). It
cites the connection, so closing the session purges it.

The rooms view reads it: a notice settled on a connection is not
carried again, so a connection to a removed member's node, once given
its notice, carries nothing and is closed (docs/REMOVAL.md).

Valid iff it cites a connection. Filed under `conn.settled.byConn [cid]`.
-/
import Connection.Recv

namespace Connection
open Engine

def Settled.check (o : Op) (room : B) : List F → Option Fact
  | [.inr (.connection ..)] => some (.settled (o.reqs.headD .empty) room)
  | _ => none

/-- Room (or notice) r settled on connection cid. -/
def Settled.op (cid r : Id) : Op := mkOp [cid] (.settled r)

namespace settled
def byConn : Rel Fact := ⟨"conn.settled", "byConn", fun | .settled c _ => some [c] | _ => none⟩
end settled

end Connection
