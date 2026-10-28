/-
`eph` (local): one ephemeral X25519 secret for one handshake, drawn at
random from the OS by the side that uses it: the initiator's `e`, the
responder's `f`. It cites the handshake op it was drawn for (the
request, or the connection), so purging the session purges it with no
search. The side's `established` op cites it. That is what leaves the
session's traffic unreadable afterwards: the transport keys depend on
`ee`, and no other copy of either secret exists.

Valid iff the secret is 32 bytes. Its fact is that op, the public key
and the secret, filed under `conn.eph.byOf [op]`.
-/
import Connection.Types

namespace Connection
open Engine

def Eph.check (K : Keys) (o : Op) (sk : B) : List F → Option Fact
  | [_] => if sk.size = 32 then some (.eph (o.reqs.headD .empty) (K.suite.pub sk) sk) else none
  | _ => none

/-- Secret `sk`, drawn for handshake op `of`. -/
def Eph.op (sk : B) (of : Id) : Op := mkOp [of] (.eph sk)

namespace eph
def byOf : Rel Fact := ⟨"conn.eph", "byOf", fun | .eph x _ _ => some [x] | _ => none⟩
end eph

end Connection
