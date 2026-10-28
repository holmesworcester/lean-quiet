/-
Two nodes syncing over an in-memory queue that may lose payloads: a
transport without sockets or a handshake, for tests. One session joins
them (`cid`, opened on both sides with `Node.connect`); a lost payload
is gone; a dropped session is reopened on both sides at once, as a
redial with a new handshake would. Each side's store is SQLite (in
memory or on disk).
-/
import Engine.Sync.Node

namespace Engine.Sync

structure Side where
  db : Db
  node : Node
  /-- This side's address, as its peer sees it. -/
  addr : ByteArray

structure Pair where
  a : Side
  b : Side
  cid : Id
  toA : List ByteArray := []
  toB : List ByteArray := []
  now : Nat := 0
  rng : UInt64 := 0x2545F4914F6CDD1D
  /-- Percent of payloads lost. -/
  loss : Nat := 0
  lost : Nat := 0
  reconnects : Nat := 0
  frames : Nat := 0

section
variable {F : Type} [Codec F] [SortKey F] (xa xb : Sync F (SqlM F))

def Pair.rand (p : Pair) (n : Nat) : Nat × Pair :=
  let s := p.rng * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, { p with rng := s })

def payloads (e : Effects) : List ByteArray := e.send.map (·.2)

def Side.run (s : Side) (f : Node → SqlM F (Node × Effects)) : IO (Side × Effects) := do
  let (n, e) ← (f s.node).run s.db
  return ({ s with node := n }, e)

/-- Open the session: a dials b. -/
def Pair.connect (p : Pair) : IO Pair := do
  let (a, ea) ← p.a.run fun n => n.connect xa p.cid p.b.addr true p.now
  let (b, eb) ← p.b.run fun n => n.connect xb p.cid p.a.addr false p.now
  return { p with a, b, toB := payloads ea, toA := payloads eb }

/-- Route what a did and what b did; a drop on either side closes both
and reopens. -/
def Pair.route (p : Pair) (ea eb : Effects) : IO Pair := do
  if !ea.drop.isEmpty || !eb.drop.isEmpty then
    let p := { p with
      a := { p.a with node := p.a.node.close p.cid }
      b := { p.b with node := p.b.node.close p.cid }
      toA := []
      toB := []
      reconnects := p.reconnects + 1 }
    p.connect xa xb
  else return { p with toB := p.toB ++ payloads ea, toA := p.toA ++ payloads eb }

/-- Deliver one payload (or lose it), or, with nothing in flight, let
`tickMs` pass and tick both sides. -/
def Pair.step (p : Pair) (tickMs : Nat) : IO Pair := do
  match p.toA, p.toB with
  | [], [] =>
    let now := p.now + tickMs
    let (a, ea) ← p.a.run fun n => n.onTick xa now
    let (b, eb) ← p.b.run fun n => n.onTick xb now
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
      let (b, eb) ← p.b.run fun n => n.onFrame xb p.a.addr f p.now
      { p with b }.route xa xb {} eb
    else
      let f := ta.head!
      let p := { p with toA := ta.tail }
      if l < p.loss then return { p with lost := p.lost + 1 }
      let (a, ea) ← p.a.run fun n => n.onFrame xa p.b.addr f p.now
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
  let (a, ea) ← p.a.run fun n => n.onWrite xa ops p.now
  { p with a }.route xa xb ea {}

def Pair.writeB (p : Pair) (ops : List Op) : IO Pair := do
  let (b, eb) ← p.b.run fun n => n.onWrite xb ops p.now
  { p with b }.route xa xb {} eb

end

end Engine.Sync
