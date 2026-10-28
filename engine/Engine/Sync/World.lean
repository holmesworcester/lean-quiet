/-
Two nodes and the network between them, as data, so a proof can run
them: each node's sync state (`Node`) and its store (`Held`), and the
frames in flight. A step runs one of a node's entry points on its held
store, the same code the runner calls on SQLite, and puts what it sends
in flight:

- deliver a frame in flight to the node at its address, as from the
  other node (`Node.onFrame`);
- tick a node (`Node.onTick`);
- a node's local write (`Node.onWrite`);
- open a session at a node toward the other (`Node.connect`, as the
  pair harness does).

The hooks are pure: a node's rooms on each connection are fixed, and
frames are sealed in the clear (`plainSeal`, `plainOpen`). The family
writes nothing else (no handshake, no couriers, no reactions), so
sessions come only from `Node.connect`.

The network is a multiset: a step may deliver any frame in flight, and
nothing else takes one out, so a frame is delivered at most once and
may wait forever. An attacker who drops, replays and injects frames is
one more kind of step.
-/
import Engine.Sync.Node

namespace Engine.Sync

/-- Which of the two nodes. -/
inductive Who where
  | a
  | b
  deriving DecidableEq, Inhabited

def Who.other : Who → Who
  | .a => .b
  | .b => .a

/-- A payload on the wire, to an address. -/
structure Frame where
  dst : ByteArray
  bytes : ByteArray
  deriving Inhabited

/-- A node: its sync state, its store, and its address as the other
node sees it. -/
structure Peer (F : Type) where
  node : Node
  held : Held F
  addr : ByteArray

structure World (F : Type) where
  a : Peer F
  b : Peer F
  /-- Frames in flight, in no order: any may be delivered next. -/
  net : List Frame := []
  now : Nat := 0

/-- What the world runs: the family, the connection settings, and each
node's rooms on each connection. -/
structure Setup (F : Type) where
  fam : Family F
  cfg : Config := {}
  rooms : Who → Id → List Id

variable {F : Type}

/-- Node s's sync: its fixed rooms, frames sealed in the clear. -/
def Setup.sync (S : Setup F) (s : Who) : Sync F (HeldM F) :=
  { fam := S.fam, cfg := S.cfg,
    hooks := { rooms := fun cid => pure (S.rooms s cid), sealFor := plainSeal, openFrame := plainOpen } }

def World.peer (w : World F) : Who → Peer F
  | .a => w.a
  | .b => w.b

def World.set (w : World F) : Who → Peer F → World F
  | .a, p => { w with a := p }
  | .b, p => { w with b := p }

/-- The frames a node's effects put in flight. -/
def frames (e : Effects) : List Frame := e.send.map fun p => ⟨p.1, p.2⟩

/-- Run an entry point at node s at time t: its node and store move on,
and what it sends joins `net`, the frames still in flight. -/
def World.run (w : World F) (s : Who) (net : List Frame) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) : World F :=
  let p := w.peer s
  let r := (f p.node).run p.held
  { w.set s { p with node := r.1.1, held := r.2 } with net := net ++ frames r.1.2, now := t }

/-- Node s takes frame f, out of `pre ++ f :: post`, from the other node. -/
def World.deliver (S : Setup F) (w : World F) (s : Who) (pre post : List Frame) (f : Frame)
    (t : Nat) : World F :=
  w.run s (pre ++ post) t fun n => n.onFrame (S.sync s) (w.peer s.other).addr f.bytes t

def World.tick (S : Setup F) (w : World F) (s : Who) (t : Nat) : World F :=
  w.run s w.net t fun n => n.onTick (S.sync s) t

def World.write (S : Setup F) (w : World F) (s : Who) (ops : List Op) (t : Nat) : World F :=
  w.run s w.net t fun n => n.onWrite (S.sync s) ops t

/-- Node s opens session cid toward the other node. -/
def World.connect (S : Setup F) (w : World F) (s : Who) (cid : Id) (dialer : Bool) (t : Nat) :
    World F :=
  w.run s w.net t fun n => n.connect (S.sync s) cid (w.peer s.other).addr dialer t

/-- One step of the world, at a time no earlier than the last. -/
inductive World.Step (S : Setup F) : World F → World F → Prop
  | deliver {w : World F} (s : Who) {pre post : List Frame} {f : Frame} {t : Nat} :
      w.net = pre ++ f :: post → f.dst = (w.peer s).addr → w.now ≤ t →
      World.Step S w (w.deliver S s pre post f t)
  | tick {w : World F} (s : Who) {t : Nat} : w.now ≤ t → World.Step S w (w.tick S s t)
  | write {w : World F} (s : Who) (ops : List Op) {t : Nat} : w.now ≤ t →
      World.Step S w (w.write S s ops t)
  | connect {w : World F} (s : Who) (cid : Id) (dialer : Bool) {t : Nat} : w.now ≤ t →
      World.Step S w (w.connect S s cid dialer t)

/-- The worlds reachable in steps. -/
inductive World.Steps (S : Setup F) : World F → World F → Prop
  | refl (w : World F) : World.Steps S w w
  | step {w w' w'' : World F} : World.Step S w w' → World.Steps S w' w'' → World.Steps S w w''

/-- A booted node with nothing stored, at an address. -/
def Peer.empty (fam : Family F) (floor : Nat) (addr : ByteArray) : Peer F :=
  { node := Node.boot fam [] floor, held := {}, addr }

/-- A session's sealed frame in the clear, carrying these payloads. -/
def plainFrame (cid : Id) (payloads : List ByteArray) : ByteArray :=
  tagged sealedTag (Codec.encode (cid, Codec.encode payloads))

end Engine.Sync
