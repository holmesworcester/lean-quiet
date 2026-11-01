import app.connection.Family

/-!
`connection.request`: how it is written.
-/

namespace Connection
open Engine Codec

/-- The request from this node (key secret `sk`) to the node whose key is
`to`, with ephemeral secret `e`, sealing `hello`. -/
def Request.op (K : Keys) (sk to e helloBytes : B) : Option Op :=
  (Noise.write1 K.suite prologue sk e to helloBytes).map fun (_, m1) =>
    mkOp [] (.request to (K.suite.pub sk) m1)

end Connection
