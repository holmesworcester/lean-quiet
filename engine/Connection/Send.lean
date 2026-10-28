/-
`send` (local): a courier, the one way out (tiny's and poc-17's
egress door). It cites the op it carries and names a route: a bare
address for the two handshake messages, or a connection. Commands write
couriers; they never send anything themselves.

The node lists `conn.send.all` and reads each carried op's bytes when it
hands the courier out (poc-17's `ship`, by reference). It then purges
the courier. Purging a session purges its couriers with it, because they
cite its ops, so no courier outlives its connection. A courier is
content-addressed, so writing the same send again is one op until the
first is purged. Valid iff the carried op is and the destination is
non-empty.
-/
import Connection.Established

namespace Connection
open Engine Engine.Sync

def Send.check (o : Op) (bare : Bool) (dest : B) : List F → Option Fact
  | [_] => if 0 < dest.size then some (.send (o.reqs.headD .empty) bare dest) else none
  | _ => none

/-- A courier carrying op x on a route. -/
def Send.op : Route → Op → Op
  | .bare a, x => mkOp [x.id] (.send true a)
  | .conn c, x => mkOp [x.id] (.send false c)

namespace send
def all : Rel Fact := ⟨"conn.send", "all", fun | .send .. => some [] | _ => none⟩
end send

end Connection
