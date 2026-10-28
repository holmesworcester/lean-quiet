/-
The send side's lanes (docs/SYNC.md, "Lanes"): what keeps a fresh op
from waiting behind a backlog on its way out. Pure, so the laws
(LaneLaws.lean) are about the functions the runner (Tcp.lean) calls.

- `Lane`: urgent (interaction: wire control naming few ids, and the ops
  this node just wrote) or serve (answers to a peer's wants and long
  offers: uiprio's `serve` class on the sending side). `wireLane` and
  `Node.serveOwed` decide which.
- `Lanes`: a socket's frames waiting for its writer, a queue per lane.
  Each native write (`take`) is every urgent frame, then serve frames up
  to `burst` bytes, at least one, so a frame longer than `burst` still
  goes.
- `framesFor`: a step's frames for one socket, those to its address, in
  order: each socket's lanes get only their own.
- `Inbox.next`: the run loop's next event, a local write before any
  frame.
-/
namespace Engine.Sync

/-- Which lane a frame takes on its way out. -/
inductive Lane where
  /-- Interaction: wire control naming few ids, and the ops this node
  just wrote. -/
  | urgent
  /-- Answers to a peer's wants, and long offers and wants: the backlog. -/
  | serve
  deriving DecidableEq, Inhabited, Repr

/-- Bytes of these frames. -/
def bytesOf (fs : List ByteArray) : Nat := (fs.map (·.size)).sum

/-- A socket's frames waiting for its writer, a queue per lane. -/
structure Lanes where
  urgent : List ByteArray := []
  serve : List ByteArray := []
  deriving Inhabited

def Lanes.push (q : Lanes) : Lane → ByteArray → Lanes
  | .urgent, f => { q with urgent := q.urgent ++ [f] }
  | .serve, f => { q with serve := q.serve ++ [f] }

/-- Pushes, in order. -/
def Lanes.pushAll (q : Lanes) (ps : List (Lane × ByteArray)) : Lanes :=
  ps.foldl (fun q p => q.push p.1 p.2) q

def Lanes.isEmpty (q : Lanes) : Bool := q.urgent.isEmpty && q.serve.isEmpty

/-- Serve bytes waiting. -/
def Lanes.queued (q : Lanes) : Nat := bytesOf q.serve

/-- Frames from the front while they fit in `room` bytes. -/
def fill (room : Nat) : List ByteArray → List ByteArray × List ByteArray
  | [] => ([], [])
  | f :: fs =>
    if f.size ≤ room then
      let (a, b) := fill (room - f.size) fs
      (f :: a, b)
    else ([], f :: fs)

/-- One burst of serve frames: the first, then what fits in `burst`
bytes with it. -/
def cut (burst : Nat) : List ByteArray → List ByteArray × List ByteArray
  | [] => ([], [])
  | f :: fs =>
    let (a, b) := fill (burst - f.size) fs
    (f :: a, b)

/-- The writer's next native write, and what it leaves: every urgent
frame, then one burst of serve frames. -/
def Lanes.take (burst : Nat) (q : Lanes) : List ByteArray × Lanes :=
  let (b, rest) := cut burst q.serve
  (q.urgent ++ b, { urgent := [], serve := rest })

/-- A step's frames, each to an address, in its lane: the last `serve`
are the serve lane's (`Effects.serve`). -/
def laned (send : List (ByteArray × ByteArray)) (serve : Nat) : List (ByteArray × Lane × ByteArray) :=
  (send.take (send.length - serve)).map (fun p => (p.1, .urgent, p.2)) ++
    (send.drop (send.length - serve)).map (fun p => (p.1, .serve, p.2))

/-- A step's frames for socket s, in order: those to an address that is
s's (`sockOf`). -/
def framesFor (sockOf : ByteArray → Option Nat) (s : Nat) (fs : List (ByteArray × Lane × ByteArray)) :
    List (Lane × ByteArray) :=
  fs.filterMap fun p => if sockOf p.1 = some s then some p.2 else none

/-- The run loop's next event: a local write waiting, else the next
event from the sockets and the listener. -/
def Inbox.next {m : Type → Type} [Monad m] {W E : Type} (writes : m (Option W)) (events : m (Option E)) :
    m (Option (W ⊕ E)) := do
  match ← writes with
  | some w => return some (.inl w)
  | none => return (← events).map .inr

end Engine.Sync
