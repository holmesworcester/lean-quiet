import app.connection.Family

/-!
`connection.connection`: how it is written.
-/

namespace Connection
open Engine Codec

/-- The answer's message 2 to request (to, frm, m1), by the node whose
key secret is `sk`, with ephemeral secret `f`. -/
def Reply.op (K : Keys) (req : Id) (sk frm m1 f : B) : Option Op := do
  let (st, re, _) ← Noise.read1 K.suite prologue sk frm m1
  let (_, m2) ← Noise.write2 K.suite st f frm re .empty
  return mkOp [req] (.connection m2)

end Connection
