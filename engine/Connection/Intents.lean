/-
The connection family's reactions and commands: views over lists that
return the ops to write. The node runs `react` after every write and
`dial` on every tick, and writes what they return. Nothing here sends,
or decides anything outside ops.

`react`, for this device:
- **open**: every request to its static key with no `opened` gets one.
- **deliver**: every opened request's hello ops go to the writer through
  `intake`. A joiner's request reaches the members this way.
- **answer**: every opened request with no connection, whose initiator
  the trust rule admits for the hello's community, gets `answer`'s ops,
  sent back to the address its `recv` names. A request the rule does not
  admit gets no reply.
- **establish**: every connection answering a request of this device's,
  with no `established`, gets this side's `established`.

`dial`, on a tick: every peer this device should hold a session with,
and has none, gets a `connect`. That's the live members of its
communities with a `seen` address, and the inviter of its pending join.
If a request is already out, only its courier is written again.

`closing cid`: the ids a closed session purges. Its established,
opened and eph ops, its settled ops, and the couriers routed to it.

Fresh ephemerals come from the OS (`Noise.randomBytes`), so `react` and
`dial` run in the node's SQLite monad.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Family

namespace Connection
open Engine Engine.Sync

/-- The trust rule (lean-net's): a live member of c by this node's
ops, or, before this device is admitted, the device its link names
while its ops know nothing of that device. -/
def trusts (c : Id) (peerEd : ByteArray) : View F Bool := sorry

/-- The rooms the peer on connection cid may see: the communities of
its session that it is trusted in. -/
def rooms (cid : Id) : SqlM F (List Id) := sorry

def react (S : Noise.Suite) (seed : ByteArray) : SqlM F (List Op) := sorry

def dial (S : Noise.Suite) (seed : ByteArray) (now : Nat) : SqlM F (List Op) := sorry

def closing (cid : Id) : SqlM F (List Id) := sorry

/-- What the node driver calls. -/
def hooks (S : Noise.Suite) (seed : ByteArray) : Hooks F := sorry

end Connection
