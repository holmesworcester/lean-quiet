/-
`eph` (local): one ephemeral X25519 secret for one handshake, drawn at
random from the OS by the side that uses it: the initiator's `e`, the
responder's `f`. The side's `established` op cites it, and a close
purges both. That is what leaves the session's traffic unreadable
afterwards: the transport keys depend on `ee`, and no other copy of
either secret exists.

Valid iff the secret is 32 bytes. Its fact is the public key and the
secret, filed under `conn.eph.byPub [pk]`, so the initiator can find the
ephemeral its request began with.
-/
import Connection.Types

namespace Connection
open Engine

def Eph.check (K : Keys) (sk : B) : List F → Option Fact
  | [] => if sk.size = 32 then some (.eph (K.suite.pub sk) sk) else none
  | _ => none

def Eph.op (sk : B) : Op := mkOp [] (.eph sk)

namespace eph
def byPub : Rel Fact := ⟨"conn.eph", "byPub", fun | .eph pk _ => some [pk] | _ => none⟩
end eph

end Connection
