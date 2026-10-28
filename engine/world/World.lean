/-
n real nodes and the network between them, as data, with one pure step,
so laws about them are proven by induction over every execution
(docs/PROOFS.md).

- **The nodes are the running code.** Node i is `Engine.Sync.Node`
  driven by its `Sync` (its family, settings and hooks), on a box of
  state `S` that a pure run of its monad `M` threads (`Setup.run`).
  `M` is any monad the node code runs in: `HeldM` for a store alone
  (`plain`), a store with entropy for the Connection family, a store
  with a cost counter for performance laws. The store in a box is
  `Setup.held`.
- **The network is data.** `flight` is the multiset of packets in
  flight: any may be delivered next, duplicated or dropped. `wire` is
  everything ever sent, in order (what an attacker on the network has
  seen). Every packet has a serial, the node that sent it (none for the
  attacker's), the address it says it came from, the address it goes to,
  and when it was sent.
- **Every way in is a step.** A delivery, a duplicate, a drop, a tick, a
  user's write (only through `Node.onWrite`, the node's write path), a
  crash and restart, a harness `connect`, and the attacker's injection
  of bytes it can make (`adv`). `World.step` is a total function; which
  acts an execution may take is `Legal`.

Executions are infinite sequences of legal acts (`Exec`); safety
invariants are proven over `Reachable` by induction on steps; liveness
takes the fairness hypotheses of engine/world/Fair.lean.
-/
import engine.wire.Node

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type}

/-- A payload on the network. -/
structure Packet (n : Nat) where
  /-- Unique per send; a duplicate gets its own, so fairness can name a copy. -/
  serial : Nat
  /-- The node that sent it: none for a duplicate or the attacker's. -/
  src : Option (Fin n)
  /-- The address the receiver sees it come from. -/
  origin : ByteArray
  /-- The address it goes to. -/
  dst : ByteArray
  bytes : ByteArray
  /-- The world's time when it was put in flight. -/
  sent : Nat

/-- What the world runs: n nodes, each with its sync (family, settings,
hooks) and address, and how a node's monad runs on its box. -/
structure Setup (F : Type) (M : Type → Type) (S : Type) [Monad M] where
  n : Nat
  sync : Fin n → Sync F M
  /-- Node i's address: what it listens on, and what its packets say they
  come from. -/
  addr : Fin n → ByteArray
  /-- A run of node code on a box, pure. -/
  run : {α : Type} → M α → S → α × S
  /-- The store in a box. -/
  held : S → Held F
  /-- Each node's window floor. -/
  floor : Fin n → Nat := fun _ => 0
  /-- What survives a crash: the store, by default all of the box. -/
  crash : S → S := id
  /-- Whether `connect` is a legal act: the in-memory harness's sessions,
  without a handshake. -/
  harness : Bool := false
  /-- What node i's user may write. -/
  honest : Fin n → List Op → Prop := fun _ _ => True
  /-- A session frame's session and payloads, read ideally (the statements'
  view of a frame, not a node's: in the clear for `plain`). -/
  peek : ByteArray → Option (Id × List ByteArray) := fun _ => none

/-- n nodes, their boxes, and the network. -/
structure World (S : Type) (n : Nat) where
  node : Fin n → Node
  box : Fin n → S
  /-- Packets in flight, in no order. -/
  flight : List (Packet n) := []
  /-- Every packet ever put in flight, in order. -/
  wire : List (Packet n) := []
  now : Nat := 0
  /-- The next packet's serial. -/
  serial : Nat := 0
  /-- Every op a user wrote, in order, with its node. -/
  wrote : List (Fin n × Op) := []
  /-- Every delivery made, in order: to which node, the bytes. -/
  delivered : List (Fin n × ByteArray) := []

/-- f with i's value replaced. -/
def upd {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (v : α) : Fin n → α :=
  fun j => if j = i then v else f j

@[simp] theorem upd_same {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (v : α) : upd f i v i = v := by
  simp [upd]

theorem upd_other {α : Type} {n : Nat} (f : Fin n → α) {i j : Fin n} (v : α) (h : j ≠ i) :
    upd f i v j = f j := by
  simp [upd, h]

/-- What happens next. -/
inductive Act (n : Nat) where
  /-- The k-th packet in flight reaches the node at its address. -/
  | deliver (k : Nat) (t : Nat)
  /-- The network copies the k-th packet in flight. -/
  | dup (k : Nat)
  /-- The network loses the k-th packet in flight. -/
  | drop (k : Nat)
  /-- Node i's clock. -/
  | tick (i : Fin n) (t : Nat)
  /-- Node i's user writes ops, through the node. -/
  | write (i : Fin n) (ops : List Op) (t : Nat)
  /-- Node i crashes and boots again from its store. -/
  | restart (i : Fin n) (t : Nat)
  /-- The harness opens session cid at node i toward node j. -/
  | connect (i j : Fin n) (cid : Id) (dialer : Bool) (t : Nat)
  /-- The attacker hands node i these bytes, as from `origin`. -/
  | inject (i : Fin n) (origin bytes : ByteArray) (t : Nat)

section
variable [Monad M] [Store F M] [Turn F M]

/-- The node at an address, if any. -/
def Setup.at? (P : Setup F M S) (a : ByteArray) : Option (Fin P.n) :=
  (List.finRange P.n).find? fun i => Decidable.decide (P.addr i = a)

/-- Node i's effects at time t as packets, serials from s. -/
def packets {n : Nat} (i : Fin n) (origin : ByteArray) (t : Nat) : Nat → List (ByteArray × ByteArray) →
    List (Packet n)
  | _, [] => []
  | s, (dst, b) :: rest => ⟨s, some i, origin, dst, b, t⟩ :: packets i origin t (s + 1) rest

/-- Run an entry point at node i at time t: its node and box move on, and
what it sends goes in flight and on the wire. -/
def World.enter (P : Setup F M S) (w : World S P.n) (i : Fin P.n) (t : Nat)
    (f : Node → M (Node × Effects)) : World S P.n :=
  let r := P.run (f (w.node i)) (w.box i)
  let ps := packets i (P.addr i) t w.serial r.1.2.send
  { w with node := upd w.node i r.1.1, box := upd w.box i r.2, flight := w.flight ++ ps,
           wire := w.wire ++ ps, now := t, serial := w.serial + ps.length }

/-- **The step.** -/
def World.step (P : Setup F M S) (w : World S P.n) : Act P.n → World S P.n
  | .deliver k t =>
    match w.flight[k]? with
    | none => w
    | some p =>
      let w' := { w with flight := w.flight.eraseIdx k }
      match P.at? p.dst with
      | none => { w' with now := t }
      | some j =>
        let w'' := w'.enter P j t fun nd => nd.onFrame (P.sync j) p.origin p.bytes t
        { w'' with delivered := w.delivered ++ [(j, p.bytes)] }
  | .dup k =>
    match w.flight[k]? with
    | none => w
    | some p => { w with flight := w.flight ++ [{ p with serial := w.serial, src := none, sent := w.now }],
                         serial := w.serial + 1 }
  | .drop k => { w with flight := w.flight.eraseIdx k }
  | .tick i t => w.enter P i t fun nd => nd.onTick (P.sync i) t
  | .write i ops t =>
    let w' := w.enter P i t fun nd => nd.onWrite (P.sync i) ops t
    { w' with wrote := w.wrote ++ ops.map (i, ·) }
  | .restart i t =>
    let b := P.crash (w.box i)
    { w with node := upd w.node i (Node.boot (P.sync i).fam (P.held b).log (P.floor i)),
             box := upd w.box i b, now := t }
  | .connect i j cid dialer t => w.enter P i t fun nd => nd.connect (P.sync i) cid (P.addr j) dialer t
  | .inject i origin b t =>
    let w' := w.enter P i t fun nd => nd.onFrame (P.sync i) origin b t
    { w' with delivered := w.delivered ++ [(i, b)] }

/-- Which acts an execution may take at w: time never goes back, a packet
named is in flight, a user writes what it may, `connect` only in the
harness, and the attacker injects only bytes it can make (`adv`). -/
def Legal (P : Setup F M S) (adv : World S P.n → ByteArray → Prop) (w : World S P.n) : Act P.n → Prop
  | .deliver k t => k < w.flight.length ∧ w.now ≤ t
  | .dup k => k < w.flight.length
  | .drop k => k < w.flight.length
  | .tick _ t => w.now ≤ t
  | .write i ops t => w.now ≤ t ∧ P.honest i ops
  | .restart _ t => w.now ≤ t
  | .connect _ _ _ _ t => P.harness = true ∧ w.now ≤ t
  | .inject _ _ b t => adv w b ∧ w.now ≤ t

/-- No attacker: nothing may be injected. -/
def noAdv {n : Nat} : World S n → ByteArray → Prop := fun _ _ => False

/-- Every node booted from its box's store, nothing in flight. -/
def World.init (P : Setup F M S) (box : Fin P.n → S) : World S P.n :=
  { node := fun i => Node.boot (P.sync i).fam (P.held (box i)).log (P.floor i), box }

/-- Acts in order. -/
def World.run (P : Setup F M S) (w : World S P.n) : List (Act P.n) → World S P.n
  | [] => w
  | a :: as => (w.step P a).run P as

/-- The worlds a legal run reaches from w₀. -/
inductive Reachable (P : Setup F M S) (adv : World S P.n → ByteArray → Prop) (w₀ : World S P.n) :
    World S P.n → Prop
  | init : Reachable P adv w₀ w₀
  | step {w : World S P.n} {a : Act P.n} : Reachable P adv w₀ w → Legal P adv w a →
      Reachable P adv w₀ (w.step P a)

/-- The k-th world of a sequence of acts from w₀. -/
def worlds (P : Setup F M S) (w₀ : World S P.n) (act : Nat → Act P.n) : Nat → World S P.n
  | 0 => w₀
  | k + 1 => (worlds P w₀ act k).step P (act k)

/-- **An execution:** an infinite sequence of legal acts from w₀. -/
structure Exec (P : Setup F M S) (adv : World S P.n → ByteArray → Prop) (w₀ : World S P.n) where
  act : Nat → Act P.n
  legal : ∀ k, Legal P adv (worlds P w₀ act k) (act k)

/-- An execution's k-th world. -/
def Exec.world {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}
    (E : Exec P adv w₀) (k : Nat) : World S P.n :=
  worlds P w₀ E.act k

theorem Exec.world_succ {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}
    (E : Exec P adv w₀) (k : Nat) : E.world (k + 1) = (E.world k).step P (E.act k) := rfl

/-- Every world of an execution is reachable. -/
theorem Exec.reachable {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}
    (E : Exec P adv w₀) : ∀ k, Reachable P adv w₀ (E.world k)
  | 0 => .init
  | k + 1 => .step (E.reachable k) (E.legal k)

end

/-! ## Reading a world -/

section
variable [Monad M]

/-- Node i's store holds op x, and x is an op of room r. -/
def Holds (P : Setup F M S) (w : World S P.n) (i : Fin P.n) (r x : Id) : Prop :=
  ∃ o, (P.held (w.box i)).db.ops x = some o ∧ (P.sync i).fam.room o = some r

/-- Node i holds session cid's connection. -/
def World.isOpen {n : Nat} (w : World S n) (i : Fin n) (cid : Id) : Prop := ((w.node i).conn? cid).isSome

end

/-! ## The plain setup: fixed rooms, frames in the clear -/

/-- A sealed frame read in the clear: its session and payloads. -/
def plainPeek (b : ByteArray) : Option (Id × List ByteArray) :=
  if (b[0]? : Option UInt8) = some sealedTag then
    (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)).bind fun p =>
      (Codec.decode p.2 : Option (List ByteArray)).map (p.1, ·)
  else none

/-- A node of the plain setup: its family and settings, fixed rooms per
session, frames sealed in the clear; its family writes nothing else. -/
def psync (fam : Family F) (cfg : Config) (rooms : Id → List Id) : Sync F (HeldM F) :=
  { fam := fam, cfg := cfg,
    hooks := { rooms := (fun cid => pure (rooms cid)), sealFor := plainSeal, openFrame := plainOpen } }

/-- n nodes on held stores, each with fixed rooms per session and frames
sealed in the clear (`plainSeal`); the family writes nothing else, so
sessions come from `connect` (a3's two-node world, for n nodes). -/
def plain (fam : Family F) (cfg : Config) (n : Nat) (addr : Fin n → ByteArray)
    (rooms : Fin n → Id → List Id) : Setup F (HeldM F) (Held F) where
  n := n
  sync i := psync fam cfg (rooms i)
  addr := addr
  run m h := m.run h
  held h := h
  harness := true
  peek := plainPeek

end Engine.World
