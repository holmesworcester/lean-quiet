/-
`seen` (local): where a device was heard from: its device key, an
address, a time. It is written from an invite link's hints, from opened
hellos, and later from mDNS answers. `dial` reads `conn.seen.byPeer
[peer]` for addresses, newest first. Valid iff the key is 32 bytes and
the address is non-empty.
-/
import Connection.Recv

namespace Connection
open Engine

def Seen.check (peer addr : B) (at_ : Nat) : List F → Option Fact
  | [] => if peer.size = 32 ∧ 0 < addr.size then some (.seen peer addr at_) else none
  | _ => none

def Seen.op (peer addr : B) (at_ : Nat) : Op := mkOp [] (.seen peer addr at_)

namespace seen
def byPeer : Rel Fact := ⟨"conn.seen", "byPeer", fun | .seen p .. => some [p] | _ => none⟩
end seen

end Connection
