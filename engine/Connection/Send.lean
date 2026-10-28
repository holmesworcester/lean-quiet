/-
`send` (local): a courier, the one way out for the two handshake
messages (tiny's and poc-17's egress door). It cites the op it carries
and names the bare address it goes to. Session traffic needs no courier:
the node seals it into frames. Commands write couriers; they never send
anything themselves.

The node lists `conn.send.all` and reads each carried op's bytes when it
hands the courier out (poc-17's `ship`, by reference). It then purges
the courier. Purging a session purges its couriers with it, because they
cite its ops. A courier is content-addressed, so writing the same send
again is one op until the first is purged. Valid iff the carried op is
and the address is non-empty.
-/
import Connection.Established

namespace Connection
open Engine

def Send.check (o : Op) (addr : B) : List F → Option Fact
  | [_] => if 0 < addr.size then some (.send (o.reqs.headD .empty) addr) else none
  | _ => none

/-- A courier carrying op x to a bare address. -/
def Send.op (addr : B) (x : Op) : Op := mkOp [x.id] (.send addr)

namespace send
def all : Rel Fact := ⟨"conn.send", "all", fun | .send .. => some [] | _ => none⟩
end send

end Connection
