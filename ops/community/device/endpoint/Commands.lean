import ops.community.Family

/-!
`community.device.endpoint`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- This node's key (local), from 32 random bytes: what it handshakes
with, and what the devices it holds name as their X25519 key. -/
def endpoint (sk : ByteArray) : Op := mkOp [] (.endpoint sk)
end Community
namespace Community
open Engine

/-- This node's key: its endpoint op's public key and secret (the least
id, should it ever hold two). -/
def nodeKey : View Fact (Option (Key × ByteArray)) := do
  let a ← endpoint.all.read [] (limit := some 1)
  pure (a.rows.head?.bind fun (_, f) => match f with
    | .endpoint pk sk => some (pk, sk)
    | _ => none)

/-- This node's key, and the op that makes it if the node has none yet,
from 32 fresh bytes: the first `found` or `join` on a node writes it. -/
def nodeKeyOr (fresh : ByteArray) : View Fact (Key × List Op) :=
  nodeKey.bind fun
    | some (pk, _) => .pure (pk, [])
    | none => .pure (cryptoSeal.pub fresh, [endpoint fresh])

end Community
