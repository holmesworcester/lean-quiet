import engine.wire.Node
import app.connection.Family
import engine.sync.Notice

/-!
`connection.established`: how it is written.
-/

namespace Connection
open Engine Codec

def Established.op (cid req eph epOp : Id) : Op := mkOp [cid, req, eph, epOp] .established

end Connection

namespace Connection
open Engine Engine.Sync Codec

/-- The peer keys connection cid's established facts name. -/
def peersOf (a : Answer F) : List B :=
  a.rights.filterMap fun (_, f) => match f with
    | .established _ _ peer .. => some peer
    | _ => none

end Connection
