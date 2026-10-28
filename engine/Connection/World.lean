/-
Two real nodes and the wire between them, as data, with a pure step, so
laws about them are proven by induction over every execution.

Each side is `Engine.Sync.Node` running the node's one family
(`Connection.node C K`) with the Connection family's real hooks
(`Connection.hooks`): dial, react, the outbox, sealing and opening
frames, closing and retiring sessions, purge. Its store is held data
(`Held`, with the engine's `Turn`), and its entropy is a stream of draws
fixed in advance (`Box.ent`), so a run is a function of its inputs.

The wire is the attacker's. Everything a node sends is appended to
`World.wire`, and nothing reaches a node except what an act delivers:
which bytes, to which node, as if from which address, and when. Which
deliveries an execution may make (only bytes the attacker can derive)
is `Connection.Wiretap`'s; this file only steps.
-/
import Connection.Intents
import Engine.Sync.Held

namespace Connection.Pair
open Engine Engine.Sync

/-- A node's store as data, its entropy, and how many draws it has
taken: the `n`-th fresh secret is `ent n`. -/
structure Box where
  held : Held F := {}
  ent : Nat → B
  draws : Nat := 0

/-- A node's runs, pure: its store and its entropy are the state. -/
def NodeM (α : Type) := Box → α × Box

instance : Monad NodeM where
  pure a := fun b => (a, b)
  bind m k := fun b => k (m b).1 (m b).2

/-- A step on the held store alone. -/
def NodeM.held {α : Type} (m : HeldM F α) : NodeM α := fun b =>
  let r := m b.held
  (r.1, { b with held := r.2 })

instance : Store F NodeM where
  getOp x := .held (Store.getOp (F := F) x)
  putOp o := .held (Store.putOp (F := F) o)
  getStatus x := .held (Store.getStatus (F := F) x)
  setStatus x v := .held (Store.setStatus (F := F) x v)
  addWait r x := .held (Store.addWait (F := F) r x)
  waiters r := .held (Store.waiters (F := F) r)
  clearWaiters r := .held (Store.clearWaiters (F := F) r)
  push x := .held (Store.push (F := F) x)
  pop := .held (Store.pop (F := F))
  index k x := .held (Store.index (F := F) k x)
  lookup k := .held (Store.lookup (F := F) k)

instance : Lists F NodeM where
  list q := .held (Lists.list q)

instance : Turn F NodeM where
  turn fam ops := .held (Turn.turn fam ops)
  purge fam ids s := .held (Turn.purge fam ids s)

/-- The next draw. -/
instance : Fresh NodeM := ⟨fun b => (b.ent b.draws, { b with draws := b.draws + 1 })⟩

/-- What both nodes run: the crypto, the sync settings, each node's
address (what it listens on, and what it puts in its hellos) and
entropy, and the seed of each node's device (its user writes the
device's `secret` op). -/
structure Setup where
  C : Community.Crypto
  K : Keys
  cfg : Config := {}
  addrA : B
  addrB : B
  entA : Nat → B
  entB : Nat → B
  seedA : B
  seedB : B

namespace Setup
variable (P : Setup)

def fam : Family F := node P.C P.K
def addr : Bool → B | true => P.addrA | false => P.addrB
def ent : Bool → Nat → B | true => P.entA | false => P.entB
def seed : Bool → B | true => P.seedA | false => P.seedB
/-- Node A's (true) or B's device key. -/
def dev (isA : Bool) : B := Community.ed25519.pub (P.seed isA)

/-- Node A's (true) or B's sync: the family and its real hooks. -/
def sync (isA : Bool) : Sync F NodeM :=
  { fam := P.fam, cfg := P.cfg, hooks := hooks P.fam P.K (P.addr isA) }

end Setup

/-- One node: its node state and its store. -/
structure Side where
  node : Node
  box : Box

/-- The pair, and everything sent between them. -/
structure World where
  a : Side
  b : Side
  /-- Every payload either node has sent, in order: whether A sent it,
  the address it was sent to, the bytes. The attacker sees all of it. -/
  wire : List (Bool × B × B) := []
  /-- Every delivery made, in order: to A or not, the bytes. -/
  delivered : List (Bool × B) := []
  /-- Every op a user wrote, in order: at A or not, the op. -/
  wrote : List (Bool × Op) := []

namespace World

def side (w : World) : Bool → Side | true => w.a | false => w.b

def set (w : World) : Bool → Side → World
  | true, s => { w with a := s }
  | false, s => { w with b := s }

/-- Both nodes booted with empty stores and no draws taken. -/
def init (P : Setup) : World :=
  { a := { node := Node.boot P.fam [] 0, box := { ent := P.entA } }
    b := { node := Node.boot P.fam [] 0, box := { ent := P.entB } } }

end World

/-- What happens next. -/
inductive Act where
  /-- These bytes reach the node, as if from address `src`. -/
  | deliver (toA : Bool) (src bytes : B) (now : Nat)
  /-- The node's clock. -/
  | tick (toA : Bool) (now : Nat)
  /-- The node's device writes ops (its user's actions). -/
  | write (toA : Bool) (ops : List Op) (now : Nat)

def Act.toA : Act → Bool
  | .deliver t .. | .tick t _ | .write t .. => t

/-- The entry point an act calls, on node A (true) or B. -/
def Setup.enter (P : Setup) (isA : Bool) (n : Node) : Act → NodeM (Node × Effects)
  | .deliver _ src bytes now => n.onFrame (P.sync isA) src bytes now
  | .tick _ now => n.onTick (P.sync isA) now
  | .write _ ops now => n.onWrite (P.sync isA) ops now

/-- **The step**: the act's node runs its entry point on its own store;
what it sends goes on the wire. -/
def World.step (P : Setup) (w : World) (a : Act) : World :=
  let isA := a.toA
  let s := w.side isA
  let r := P.enter isA s.node a s.box
  let w' := w.set isA { node := r.1.1, box := r.2 }
  { w' with
    wire := w.wire ++ r.1.2.send.map fun (to, bytes) => (isA, to, bytes)
    delivered := match a with
      | .deliver t _ bytes _ => w.delivered ++ [(t, bytes)]
      | _ => w.delivered
    wrote := match a with
      | .write t ops _ => w.wrote ++ ops.map (t, ·)
      | _ => w.wrote }

/-- The ops node A (true) or B holds. -/
def World.ops (w : World) (isA : Bool) : List Op := (w.side isA).box.held.log

/-- A read on node A's (true) or B's store. -/
def World.at (w : World) (isA : Bool) {α : Type} (m : NodeM α) : α := (m (w.side isA).box).1

/-- The sessions node A (true) or B has established: op and fact. -/
def World.ests (w : World) (isA : Bool) : List (Id × Fact) := w.at isA (rows established.all [])

/-- Acts in order. -/
def World.run (P : Setup) (w : World) : List Act → World
  | [] => w
  | a :: as => (w.step P a).run P as

end Connection.Pair
