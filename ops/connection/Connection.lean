/-
`connection` (conn scope): Noise message 2 (`e, ee, se`), the
responder's answer, as in poc-17's conn.connection. It cites the request
it answers. **Its op id is the connection id**: both ends hold the same
bytes, so both name the session the same way. The id depends on the
responder's fresh ephemeral, so nobody can name a session ahead of it.

Valid iff it cites a Valid request and holds an ephemeral key and a
tag. This is structural, like the request. Filed under
`conn.connection.byRequest [r]`.

`answer` writes the connection op, after `react` has applied the trust
rule. It writes an `eph`, the connection, this side's `established`, and
a courier carrying the connection's bytes back to the address the
request arrived from.
-/
import Connection.Opened

namespace Connection
open Engine

def Reply.check (o : Op) (m2 : B) : List F → Option Fact
  | [.inr (.request ..)] => if 48 ≤ m2.size then some (.connection (o.reqs.headD .empty) m2) else none
  | _ => none

namespace connection
def byRequest : Rel Fact := ⟨"conn.connection", "byRequest", fun | .connection r _ => some [r] | _ => none⟩
end connection

/-- The answer's message 2 to request (to, frm, m1), by device `seed`
with ephemeral secret `f`. -/
def Reply.op (K : Keys) (req : Id) (seed frm m1 f : B) : Option Op := do
  let (st, re, _) ← Noise.read1 K.suite prologue (K.xSec seed) (K.xPub frm) m1
  let (_, m2) ← Noise.write2 K.suite st f (K.xPub frm) re .empty
  return mkOp [req] (.connection m2)

end Connection
