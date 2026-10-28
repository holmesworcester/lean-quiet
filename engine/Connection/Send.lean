/-
`send` (local): a courier, the one way out (tiny's and poc-17's
egress door). It carries a route (a connection id, or a bare address
for the two handshake messages) and the bytes to send, which are an
op's own bytes. Commands write couriers; they never send anything.

The node lists `conn.send.all`, hands each courier's bytes to its route,
and purges the courier. A courier is content-addressed, so writing the
same send again is one op until the first is purged. Valid iff its
destination is non-empty.
-/
import Connection.Established

namespace Connection
open Engine Engine.Sync

def Send.check (bare : Bool) (dest bytes : B) : List F → Option Fact
  | [] => if 0 < dest.size then some (.send bare dest bytes) else none
  | _ => none

def Send.op : Route → B → Op
  | .bare a, x => mkOp [] (.send true a x)
  | .conn c, x => mkOp [] (.send false c x)

namespace send
def all : Rel Fact := ⟨"conn.send", "all", fun | .send .. => some [] | _ => none⟩
end send

end Connection
