/-
`established` (local): this side's session. It cites the connection,
the request it answers, this side's ephemeral and this node's
`endpoint`, whose secret is this side's static. Its validator re-runs this side's half of the handshake from
the cited facts:
- **Responder** (the request is to this node's key): `read1`, then
  `write2` with its ephemeral, which must give the connection's message.
- **Initiator** (the request is from this node's key): `sent1` recovers
  its state from its own message 1, so the request is its own, then
  `read2` on the connection's message.
It is Valid iff that succeeds.

Its fact is the session: the connection id, the community its hello
named, the peer's node key, the handshake hash, the two transport keys, and whether
this side dialed. The node seals frames with the keys from here. Filed
under `conn.established.all` and `conn.established.byConn [cid]`. A close
purges it.
-/
import ops.connection.Connection

namespace Connection
open Engine Codec

def Established.check (K : Keys) (o : Op) : List F → Option Fact
  | [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph _ _ esk), .inl (.endpoint pk sk)] =>
    let cid := o.reqs.headD .empty
    if o.reqs.getD 1 .empty ≠ r then none
    else if pk = to then do
      -- the responder
      let (st, re, p1) ← Noise.read1 K.suite prologue sk frm m1
      let (c, _, _) ← (decode p1 : Option (B × B × List B))
      let (sr, m2') ← Noise.write2 K.suite st esk frm re .empty
      if m2' ≠ m2 then none
      else some (.established cid c frm sr.h sr.send.k sr.recv.k false)
    else if pk = frm then do
      -- the initiator
      let (st, p1) ← Noise.sent1 K.suite prologue sk esk to m1
      let (c, _, _) ← (decode p1 : Option (B × B × List B))
      let (si, _) ← Noise.read2 K.suite st sk esk m2
      some (.established cid c to si.h si.send.k si.recv.k true)
    else none
  | _ => none

def Established.op (cid req eph epOp : Id) : Op := mkOp [cid, req, eph, epOp] .established

namespace established
def all : Rel Fact := ⟨"conn.established", "all", fun | .established .. => some [] | _ => none⟩
def byConn : Rel Fact := ⟨"conn.established", "byConn", fun | .established i .. => some [i] | _ => none⟩
end established

end Connection
