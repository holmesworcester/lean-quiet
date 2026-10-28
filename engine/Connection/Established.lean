/-
`established` (local): this side's session. It cites the connection
and this side's ephemeral, plus, for the initiator, its request and
its `secret`, or, for the responder, its `opened`. Its validator
re-runs this side's half of the handshake from the cited facts:
- the initiator rebuilds message 1 from its seed and ephemeral, and
  requires that it is the request's (so the request is its own), then
  runs `read2` on the connection's message;
- the responder runs `write2` from its opened state and ephemeral, and
  requires that it is the connection's message.
It is Valid iff that succeeds.

Its fact is the session: the connection id, the community, the peer's
static key, the handshake hash, and the two transport keys. The node's
sealing reads the keys from here. It is filed under `established.all`
and `established.byPeer [peer]`. A close purges it.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Connection

namespace Connection
open Engine

structure Established where

def Established.kind : UInt8 := 36

structure Session where
  cid : Id
  community : Id
  peer : ByteArray
  h : ByteArray
  send : Noise.Cipher
  recv : Noise.Cipher

/-- The initiator's side. -/
def Established.checkI (S : Noise.Suite) (cid : Id) (req : Request) (m2 seed e : ByteArray) :
    Option Session := sorry

/-- The responder's side. -/
def Established.checkR (S : Noise.Suite) (cid : Id) (op : OpenedFact) (m2 f : ByteArray) :
    Option Session := sorry

def Established.op (reqs : List Id) : Op := sorry

end Connection
