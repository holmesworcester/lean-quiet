/-
Executions of the production node and connection hooks. Unlike Sync.World,
sessions open through Noise and the actual connection reactions; frames use
the native AEAD and rooms are read from the store. The store is Held, whose
interpreter is explicit, and entropy is an input tape. SQLite, the OS entropy
source and TCP are tested separately by JoinFair, not silently identified with
this interpreter. No direct Node.connect or plaintext session hook is used.
-/
import ops.connection.Intents

namespace Connection.Execution
open Engine Engine.Sync Community

inductive Side where
  | a | b
  deriving DecidableEq, Inhabited

structure Memory where
  held : Held F := {}
  /-- An input, not a claim that deterministic fixtures are secure randomness. -/
  entropy : Nat → ByteArray
  cursor : Nat := 0
  /-- Durable per-peer retry metadata, kept across disposable sessions. -/
  retries : Id → Option Sweep := fun _ => none

def M (α : Type) := Memory → α × Memory

instance : Monad M where
  pure a := fun s => (a, s)
  bind x f := fun s => let (a, s') := x s; f a s'

def lift {α : Type} (x : HeldM F α) : M α := fun s =>
  let (a, h) := x s.held
  (a, { s with held := h })

instance : Store F M where
  getOp x := lift (Store.getOp x)
  putOp o := lift (Store.putOp o)
  getStatus x := lift (Store.getStatus x)
  setStatus x v := lift (Store.setStatus x v)
  addWait x y := lift (Store.addWait x y)
  waiters x := lift (Store.waiters x)
  clearWaiters x := lift (Store.clearWaiters x)
  push x := lift (Store.push x)
  pop := lift Store.pop
  index k x := lift (Store.index k x)
  lookup k := lift (Store.lookup k)
  dependents x := lift (Store.dependents x)
  undecide x := lift (Store.undecide x)
  deleteOp x := lift (Store.deleteOp x)
  countOps := lift Store.countOps

instance : Lists F M where
  list q := lift (Lists.list q)

instance : Turn F M where
  turn fam ops := lift (Turn.turn fam ops)
  purge fam ids scrub := lift (Turn.purge fam ids scrub)

instance : Fresh M where
  fresh := fun s => (s.entropy s.cursor, { s with cursor := s.cursor + 1 })

def family : Family F := Connection.node ed25519 sodium

structure Peer where
  node : Engine.Sync.Node
  memory : Memory

structure Packet where
  src : ByteArray
  dst : ByteArray
  bytes : ByteArray
  deriving DecidableEq

structure World where
  a : Peer
  b : Peer
  net : List Packet := []
  now : Nat := 0
  /-- Socket-close requests whose external transport effect this interpreter
  has not modeled. Finite native success certificates require this to stay
  zero. The infinite fairness theorem alone does not assert that it does. -/
  unhandledDrops : Nat := 0

structure Setup where
  addr : Side → ByteArray
  cfg : Config := { every := 30000, askTime := 20000 }
  /-- Flow-control input, in the same form the runner supplies to Sync. -/
  room : Side → ByteArray → Option Nat := fun _ _ => none

def Setup.sync (S : Setup) (side : Side) : Sync F M :=
  { fam := family
    cfg := S.cfg
    hooks := Connection.hooks family sodium (S.addr side)
    room := S.room side
    catalog := some {
      ceiling := lift (Catalog.held family).ceiling
      read := fun seq => lift ((Catalog.held family).read seq) }
    retryStore := some {
      load := fun peer s => ((s.retries peer).getD {}, s)
      save := fun peer cursor s => ((), { s with retries := fun p => if p = peer then some cursor else s.retries p }) } }

def World.peer (w : World) : Side → Peer
  | .a => w.a
  | .b => w.b

def World.set (w : World) : Side → Peer → World
  | .a, p => { w with a := p }
  | .b, p => { w with b := p }

def packets (S : Setup) (side : Side) (e : Effects) : List Packet :=
  e.send.map fun (addr, bytes) => ⟨S.addr side, addr, bytes⟩

def World.run (S : Setup) (w : World) (side : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects))
    (transportClosed : Bool := false) : World :=
  let p := w.peer side
  let ((n, e), memory) := f p.node p.memory
  { w.set side ⟨n, memory⟩ with
    net := queue ++ packets S side e
    unhandledDrops := w.unhandledDrops + (if transportClosed then 0 else e.drop.length) }

/-- Environment actions. Close discards buffered transport frames and notifies
both actual nodes; surviving join/admission ops must drive any redial. -/
inductive Action where
  | tick (side : Side)
  | write (side : Side) (ops : List Op)
  | deliver
  | close
  | drop
  | idle

/-- Deliver only the FIFO head. An address outside this two-node environment
has no receiver; it is discarded explicitly rather than sent to the wrong node. -/
def World.deliver (S : Setup) (w : World) : World :=
  match w.net with
  | [] => w
  | p :: rest =>
    if p.dst = S.addr .a then
      w.run S .a rest fun n => n.onFrame (S.sync .a) p.src p.bytes w.now
    else if p.dst = S.addr .b then
      w.run S .b rest fun n => n.onFrame (S.sync .b) p.src p.bytes w.now
    else { w with net := rest }

/-- One completed iteration. Time advances even when queues are empty.
This is simulated time, not a promise about OS scheduling or I/O duration. -/
def step (S : Setup) (w : World) (a : Action) : World :=
  let w' := match a with
    | .tick s => w.run S s w.net fun n => n.onTick (S.sync s) w.now
    | .write s ops => w.run S s w.net fun n => n.onWrite (S.sync s) ops w.now
    | .deliver => w.deliver S
    | .close =>
      -- This explicit environment action already closes both sides and
      -- discards buffered frames. Earlier unhandled effects stay recorded.
      let a := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
      a.run S .b a.net (fun n => n.onClose (S.sync .b) (S.addr .a) w.now) true
    | .drop => { w with net := w.net.tail }
    | .idle => w
  { w' with now := w.now + 1 }

def trace (S : Setup) (w : World) : List Action → World
  | [] => w
  | a :: rest => trace S (step S w a) rest

/-- A fair tail: both nodes tick, and the FIFO head is offered to its real
destination each cycle. Approval is an explicit local write in the prefix. -/
def schedule (i : Nat) : Action :=
  if i % 3 = 0 then .tick .a else if i % 3 = 1 then .tick .b else .deliver

def states (S : Setup) (initial : World) : Nat → World
  | 0 => initial
  | n + 1 => step S (states S initial n) (schedule n)

def dequeued (w : World) : Action → Option Packet
  | .deliver => w.net.head?
  | _ => none

structure Run (S : Setup) (initial : World) where
  state : Nat → World
  action : Nat → Action
  zero : state 0 = initial
  next : ∀ i, state (i + 1) = step S (state i) (action i)

def fairRun (S : Setup) (initial : World) : Run S initial :=
  ⟨states S initial, schedule, rfl, fun _ => rfl⟩

/-- Scheduler/transport fairness in this explicit two-node interpreter. A
queued packet reaches its addressed handler if that address is one of the
two peers. This says nothing about whether that handler accepts its bytes. -/
def Run.Fair {S initial} (r : Run S initial) : Prop :=
  (∀ N, ∃ i ≥ N, r.action i = .tick .a) ∧
  (∀ N, ∃ i ≥ N, r.action i = .tick .b) ∧
  (∀ n p, p ∈ (r.state n).net → ∃ i ≥ n, dequeued (r.state i) (r.action i) = some p) ∧
  (∀ i, (r.state i).now = initial.now + i)

def empty (ea eb : Nat → ByteArray) : World :=
  { a := ⟨Engine.Sync.Node.boot family [] 0, { entropy := ea }⟩,
    b := ⟨Engine.Sync.Node.boot family [] 0, { entropy := eb }⟩ }

end Connection.Execution
