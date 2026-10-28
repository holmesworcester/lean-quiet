/-
Two nodes syncing over an in-memory queue that may lose frames: a
transport without sockets, for tests here and the daemon's. One
connection joins them (`cid`); a lost frame is gone; a dropped
connection is reopened at once, as a daemon redials. Bare-wire frames
travel the same queue and arrive through `onBare`.
-/
import Engine.Sync.Node

namespace Engine.Sync

/-- A frame in flight: bare or on the session, and its bytes. -/
abbrev Frame := Bool × ByteArray

structure Pair where
  a : Node
  b : Node
  cid : Id
  toA : List Frame := []
  toB : List Frame := []
  now : Nat := 0
  rng : UInt64 := 0x2545F4914F6CDD1D
  /-- Percent of frames lost. -/
  loss : Nat := 0
  lost : Nat := 0
  reconnects : Nat := 0
  frames : Nat := 0

section
variable {F : Type} [Codec F] [SortKey F] (xa xb : Sync F)

def Pair.rand (p : Pair) (n : Nat) : Nat × Pair :=
  let s := p.rng * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, { p with rng := s })

def framesOf (e : Effects) : List Frame :=
  e.send.map fun (r, b) => match r with | .conn _ => (false, b) | .bare _ => (true, b)

/-- Open the connection: a dials b. -/
def Pair.connect (p : Pair) : IO Pair := do
  let (a, ea) ← p.a.connect xa p.cid true p.now
  let (b, eb) ← p.b.connect xb p.cid false p.now
  return { p with a, b, toB := framesOf ea, toA := framesOf eb }

/-- Route what a did and what b did; a drop on either side closes both
and redials. -/
def Pair.route (p : Pair) (ea eb : Effects) : IO Pair := do
  if !ea.drop.isEmpty || !eb.drop.isEmpty then
    let p := { p with
      a := p.a.close p.cid
      b := p.b.close p.cid
      toA := []
      toB := []
      reconnects := p.reconnects + 1 }
    p.connect xa xb
  else return { p with toB := p.toB ++ framesOf ea, toA := p.toA ++ framesOf eb }

def Pair.deliver (x : Sync F) (n : Node) (cid : Id) (f : Frame) (now : Nat) : IO (Node × Effects) :=
  if f.1 then n.onBare x .empty f.2 now else n.onBytes x cid f.2 now

/-- Deliver one frame (or lose it), or, with nothing in flight, let
`tickMs` pass and tick both sides. -/
def Pair.step (p : Pair) (tickMs : Nat) : IO Pair := do
  match p.toA, p.toB with
  | [], [] =>
    let now := p.now + tickMs
    let (a, ea) ← p.a.onTick xa now
    let (b, eb) ← p.b.onTick xb now
    { p with a, b, now }.route xa xb ea eb
  | ta, tb =>
    let (dir, p) := p.rand 2
    let toB := !tb.isEmpty && (ta.isEmpty || dir == 0)
    let (l, p) := p.rand 100
    let p := { p with now := p.now + 1, frames := p.frames + 1 }
    if toB then
      let f := tb.head!
      let p := { p with toB := tb.tail }
      if l < p.loss then return { p with lost := p.lost + 1 }
      let (b, eb) ← Pair.deliver xb p.b p.cid f p.now
      { p with b }.route xa xb {} eb
    else
      let f := ta.head!
      let p := { p with toA := ta.tail }
      if l < p.loss then return { p with lost := p.lost + 1 }
      let (a, ea) ← Pair.deliver xa p.a p.cid f p.now
      { p with a }.route xa xb ea {}

/-- Run until the clock reaches `stop` (at most `fuel` steps). -/
def Pair.run (p : Pair) (stop tickMs fuel : Nat) : IO Pair := do
  let mut p := p
  for _ in [0:fuel] do
    if p.now ≥ stop then break
    p ← p.step xa xb tickMs
  return p

/-- A local write at a, or at b. -/
def Pair.writeA (p : Pair) (ops : List Op) : IO Pair := do
  let (a, ea) ← p.a.onWrite xa ops p.now
  { p with a }.route xa xb ea {}

def Pair.writeB (p : Pair) (ops : List Op) : IO Pair := do
  let (b, eb) ← p.b.onWrite xb ops p.now
  { p with b }.route xa xb {} eb

end

end Engine.Sync
