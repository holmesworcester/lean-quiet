/-
The connection family: its ops' bodies and facts, its validator, its
relations, and where each op travels. The request and the connection
travel on the bare wire (conn scope); every other op is local. It reads
Community's facts as well as its own, for the device secret, so the
node's one family is the two composed (`Engine.Family.sum`).

Also here: the hooks the node driver calls (`Engine.Sync.Node`):
- the rooms a connection's peer may see: the trust rule over
  Community's lists;
- the `recv` and `settled` ops;
- the couriers waiting;
- what a close purges;
- the reactions the node runs after every write (Intents).

Kinds 32–40 until the registry names them.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Settled
import Engine.Families
import Engine.Purge
import Community

namespace Connection
open Engine Engine.Sync

inductive Body where
  | eph (b : Eph)
  | request (b : Request)
  | opened
  | connection (b : Reply)
  | established
  | send (b : Send)
  | recv (b : Recv)
  | seen (b : Seen)
  | settled (b : Settled)

inductive Fact where
  | eph (pk sk : ByteArray)
  | request (to frm : ByteArray)
  | opened (f : OpenedFact)
  | connection (request : Id)
  | established (s : Session)
  | send (route : Route) (bytes : ByteArray)
  | recv (op : Id) (via : Option Id) (addr : ByteArray) (at_ : Nat)
  | seen (peer addr : ByteArray) (at_ : Nat)
  | settled (cid room : Id)

instance : Inhabited Fact := ⟨.connection .empty⟩

/-- Each op type's validator, over the facts its requirements gave
(Community's and this family's). -/
def validate (S : Noise.Suite) : Op → List (Community.Fact ⊕ Fact) → Option Fact := sorry

/-- request.byTo, opened.all, connection.byRequest, established.all,
established.byPeer, send.all, recv.byOp, seen.byPeer, settled.byConn. -/
def rels : List (Rel Fact) := sorry

def keys : Fact → List ByteArray := keysOf rels

/-- The request and the connection go on the bare wire; the rest is local. -/
def scopeOf (o : Op) : Scope := sorry

def family (S : Noise.Suite) : Family₂ Community.Fact Fact :=
  { validate := validate S, keys, scope := scopeOf, owns := fun k => 32 ≤ k ∧ k ≤ 40 }

/-- The node's facts: Community's and the connection family's. -/
abbrev F := Community.Fact ⊕ Fact

/-- The node's one family. -/
def node (C : Community.Crypto) (S : Noise.Suite) : Family F := Family.sum (Community.family C) (family S)

end Connection
