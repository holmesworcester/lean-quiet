import engine.wire.Noise
import engine.core.Engine

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

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
app/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Established

/-- What its author writes. -/
structure Body where
  deriving BEq

instance : Codec Body := Codec.tagged 36 (fun _ => ()) (fun _ => {}) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = [36] := rfl

/-- Its fact, `established`. -/
structure Fact where
  cid : B
  c : B
  peer : B
  h : B
  sendKey : B
  recvKey : B
  dialer : Bool
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 4 (fun x => (x.cid, x.c, x.peer, x.h, x.sendKey, x.recvKey, x.dialer)) (fun (p : B × B × B × B × B × B × Bool) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 4 :: Codec.enc (x.cid, x.c, x.peer, x.h, x.sendKey, x.recvKey, x.dialer) := rfl

/-! ## The lists its fact is filed in (`conn.established.*`) -/
def all : Rel Fact := ⟨"conn.established", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl
def byConn : Rel Fact := ⟨"conn.established", "byConn", fun f => some [f.cid]⟩
@[simp] theorem byConn_args (f : Fact) : byConn.args f = (some [f.cid]) := rfl

end Established

end Connection
