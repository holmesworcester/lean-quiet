/-
`request` (conn scope: the bare wire, one peer, never synced): Noise
message 1 (`e, es, ss`), as poc-17's conn.request and tiny's
connection.request. It goes to the responder's device key from the
initiator's. Both are in the clear, as poc-17's are, so the responder
can decide to answer before it opens anything. It carries the message:
the initiator's ephemeral key, then the sealed hello.

The hello is the community the initiator dials for, the address it
listens on, and the ops it delivers. A joiner's request rides here, so
it reaches the inviter before anyone approves it, and it opens nothing:
"a request alone opens nothing and earns no reply".

Valid iff both device keys convert to X25519 keys, they differ, and the
message holds an ephemeral key and a tag. This is structural, so every
holder judges it the same. Filed under `conn.request.byTo [to]` (how a
responder finds what is addressed to it) and `conn.request.byFrm [frm]`
(a dialer's own requests).

`connect` is the command: an `eph` (local), the request, and a `send`
courier carrying the request's bytes to the address. Redialing only
writes the courier again: the request is the same op, with the same
bytes and the same id.
-/
import ops.connection.Eph

namespace Connection
open Engine Engine.Sync

def Request.check (K : Keys) (to frm m1 : B) : List F → Option Fact
  | [] =>
    if to.size = 32 ∧ frm.size = 32 ∧ to ≠ frm ∧ (K.xPub to).size = 32 ∧ (K.xPub frm).size = 32 ∧
      48 ≤ m1.size
    then some (.request to frm m1) else none
  | _ => none

namespace request
def byTo : Rel Fact := ⟨"conn.request", "byTo", fun | .request t _ _ => some [t] | _ => none⟩
def byFrm : Rel Fact := ⟨"conn.request", "byFrm", fun | .request _ f _ => some [f] | _ => none⟩
end request

/-- The request from device `seed` to device key `to`, with ephemeral
secret `e`, sealing `hello`. -/
def Request.op (K : Keys) (seed to e helloBytes : B) : Option Op :=
  let frm := Community.ed25519.pub seed
  (Noise.write1 K.suite prologue (K.xSec seed) e (K.xPub to) helloBytes).map fun (_, m1) =>
    mkOp [] (.request to frm m1)

end Connection
