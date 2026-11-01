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

namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- Durable retry identity comes only from this session's authenticated
established fact. Session ids change on reconnect; the peer key does not.
An absent established fact disables catalog sends. -/
def retryKey (cid : Id) : m (Option Id) := do
  let fs ← rows established.byConn [cid]
  return fs.findSome? fun (_, f) => match f with
    | .established _ _ peer .. => some peer
    | _ => none

end
end Connection
