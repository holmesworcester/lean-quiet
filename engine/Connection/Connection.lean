/-
`connection` (conn scope): Noise message 2 (`e, ee, se`), the
responder's answer, as poc-17's conn.connection. It cites the request
it answers. **Its op id is the connection id**: both ends hold the
same bytes, so both name the session the same, and the id depends on
the responder's fresh ephemeral, so nobody can name a session ahead of
it.

Valid iff it cites a Valid request and holds an ephemeral key and a
tag: structural, like the request. It is filed under
`connection.byRequest [r]`.

`answer` is the command, run only for a peer the trust rule admits:
an `eph`, the connection, this side's `established`, and a courier for
the connection's bytes back to the address the request arrived from.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Opened

namespace Connection
open Engine

structure Reply where
  m2 : ByteArray

def Reply.kind : UInt8 := 35

def Reply.check (b : Reply) : Bool := sorry

/-- Answer opened request `op` (its op id `openedId`) with ephemeral
secret `f`, back to `addr`: the ops to write. -/
def answer (S : Noise.Suite) (openedId : Id) (op : OpenedFact) (f addr : ByteArray) : List Op := sorry

end Connection
