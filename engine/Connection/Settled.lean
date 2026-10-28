/-
`settled` (local): a room first settled on a connection (sync agreed
with this peer once). It cites the connection, and a close purges it
with the session. A screen shows "joining" until a connection has
settled the community, and reads admission and members after that.
-/
import Connection.Seen

namespace Connection
open Engine

def Settled.check (o : Op) (room : B) : List F → Option Fact
  | [.inr (.connection ..)] => some (.settled (o.reqs.headD .empty) room)
  | _ => none

def Settled.op (cid room : Id) : Op := mkOp [cid] (.settled room)

namespace settled
def byConn : Rel Fact := ⟨"conn.settled", "byConn", fun | .settled i _ => some [i] | _ => none⟩
def byRoom : Rel Fact := ⟨"conn.settled", "byRoom", fun | .settled _ r => some [r] | _ => none⟩
end settled

end Connection
