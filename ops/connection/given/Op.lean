import engine.wire.Noise
import engine.core.Engine

/-
`given` (local): the notice of removal x was given on connection cid
(docs/REMOVAL.md). When a node decides a removal, each session with the
removed member's node carries a notice (`roomsV`): the removal and its
requirement closure, given once (`Conn.give`); the node then writes this
op. It cites the connection, so closing the session purges it.

Why it is an op: the rooms view reads it. A notice given on a session
is not carried again, so the session then carries nothing and is closed
(`notice_then_cut`). Without it, the view would carry the notice for as
long as the session lives: the session would never close, and a session
reopened from its ops (a restart) would give the notice again, as would
a connection's memory, which dies with it.

Valid iff it cites a connection. Filed under `conn.given.byConn [cid]`.

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
ops/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Given

/-- What its author writes. -/
structure Body where
  x : B
  deriving BEq

instance : Codec Body := Codec.tagged 39 (fun x => x.x) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 39 :: Codec.enc x.x := rfl

/-- Its fact, `given`. -/
structure Fact where
  conn : B
  x : B
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 7 (fun x => (x.conn, x.x)) (fun (p : B × B) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 7 :: Codec.enc (x.conn, x.x) := rfl

/-! ## The lists its fact is filed in (`conn.given.*`) -/
def byConn : Rel Fact := ⟨"conn.given", "byConn", fun f => some [f.conn]⟩
@[simp] theorem byConn_args (f : Fact) : byConn.args f = (some [f.conn]) := rfl

end Given

end Connection
