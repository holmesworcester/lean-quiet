/-
A windowed node over a room with old requirements (docs/SYNC.md,
"Windows and order"). A full node holds a community's history; a node
that keeps the last day (its floor) dials it. Within the last day there
are new messages, and reactions to old messages: one to a child post of
an old clump (so the reaction needs the child, and the child its clump's
root, two steps below the window), one to an old root post. Older
messages nobody in the window cites stay old.

Checked: the windowed node ends with exactly the window, its whole
requirement closure and nothing else; every op of the window is Valid
there; and the closure arrives in the window's own round: the flight it
completes in is the window's. Flights (every frame in flight delivered,
then the next) are counted to the window and to its closure, and printed.

The cut: with depth 1, the child arrives but its clump's root (two steps
down) does not, so the child and the reaction on it stay Missing and are
listed nowhere, while the rest of the window is Valid and listed.
-/
import tests.engine.Lib

open Engine Engine.Sync Community Tests

namespace WindowSync

def C := ed25519
def fam := family C

def day : Nat := 1440
def now : Nat := 29340000
def floor : Nat := now - day

structure Room where
  c : Id
  base : List Op
  /-- Old, cited by nothing in the window. -/
  old : List Op
  /-- Old, cited by the window: its closure. -/
  need : List Op
  /-- The last day. -/
  win : List Op
  /-- The child, the reaction on it, the clump's root. -/
  child : Op
  onChild : Op
  root : Op

def room : Room := Id.run do
  let seed := sha256 "window founder".toUTF8
  let d := Device.ofSeed seed
  let k := Bytes.digest "window content key".toUTF8
  let nk := Bytes.digest "window node key".toUTF8
  let w := (found seed "Window".toUTF8 "Ann".toUTF8 1 k (Bytes.digest "window esk".toUTF8) nk).eval DB.empty
  let c := (root d (cryptoSeal.pub nk)).id
  let nonce (s : String) := Bytes.fit 24 (sha256 s.toUTF8)
  let p (i t : Nat) (clump : Option Id := none) := sealedPost c c d k (nonce s!"post {i}") s!"message {i}".toUTF8 i t clump
  -- old: a clump (root and child) five days ago, an old root post, and filler
  let r0 := p 1 (now - 5 * day)
  let c1 := p 2 (now - 5 * day + 1) (some r0.id)
  let r1 := p 3 (now - 4 * day)
  let filler := (List.range 20).map fun i => p (10 + i) (now - 3 * day + i)
  -- the last day: new messages, a reaction to the child, one to r1
  let fresh := (List.range 5).map fun i => p (100 + i) (now - 100 + i)
  let onChild := react c c c1.id d "👍".toUTF8 (now - 10)
  let onOld := react c c r1.id d "🎉".toUTF8 (now - 9)
  return { c, base := w.ops, old := filler, need := [r0, c1, r1], win := fresh ++ [onChild, onOld],
           child := c1, onChild, root := r0 }

def sync (rooms : List Id) (depth : Nat) : Sync Fact (SqlM Fact) :=
  { fam, cfg := { params := { depth } },
    hooks := { rooms := fun _ => pure (rooms.map .sync), sealFor := plainSeal, openFrame := plainOpen } }

def side (ops : List Op) (floor : Nat) (addr : String) : IO Side := do
  let db ← Db.openAt ":memory:"
  (receive fam (intake fam true ops)).run db
  return { db, node := Node.boot fam (← (dumpOps (F := Fact)).run db) floor, addr := addr.toUTF8 }

/-- Run b (dialing a) in flights until quiet: what b stored in each flight. -/
def run (x : Sync Fact (SqlM Fact)) (a b : Side) (limit : Nat := 400) : IO (Array (List Id) × Side) := do
  let cid := sha256 "window session".toUTF8
  let (b, eb) ← b.run fun nd => nd.connect x cid "a".toUTF8 true 0
  let (a, ea) ← a.run fun nd => nd.connect x cid "b".toUTF8 false 0
  let mut a := a
  let mut b := b
  let mut toA := payloads eb
  let mut toB := payloads ea
  let mut flights : Array (List Id) := #[]
  let mut now := 0
  let mut idle := 0
  while flights.size < limit && idle < 5 do
    now := now + 1000
    let mut got : List Id := []
    if toA.isEmpty && toB.isEmpty then
      let (a', e1) ← a.run fun nd => nd.onTick x now
      let (b', e2) ← b.run fun nd => nd.onTick x now
      a := a'; b := b'
      got := e2.stored
      toB := payloads e1; toA := payloads e2
    else
      let (fa, fb) := (toA, toB)
      toA := []; toB := []
      for f in fb do
        let (b', e) ← b.run fun nd => nd.onFrame x "a".toUTF8 f now
        b := b'
        got := got ++ e.stored
        toA := toA ++ payloads e
      for f in fa do
        let (a', e) ← a.run fun nd => nd.onFrame x "b".toUTF8 f now
        a := a'
        toB := toB ++ payloads e
    flights := flights.push got
    idle := if got.isEmpty && toA.isEmpty && toB.isEmpty then idle + 1 else 0
  return (flights, b)

/-- The first flight by which b holds all of `ids`, if any. -/
def doneAt (flights : Array (List Id)) (ids : List Id) : Option Nat := Id.run do
  let mut held : Std.HashSet Id := {}
  for i in [0:flights.size] do
    held := flights[i]!.foldl (·.insert ·) held
    if ids.all held.contains then return some (i + 1)
  return none

/-- Whether b judged x Valid. -/
def valid (s : Side) (x : Id) : IO Bool := do
  return match ← (Store.getStatus x : SqlM Fact _).run s.db with
    | some (.valid _) => true
    | _ => false

/-- Whether b holds x (judged or not). -/
def holds (s : Side) (x : Id) : IO Bool := do
  return (← (Store.getOp (F := Fact) x : SqlM Fact _).run s.db).isSome

/-- The messages b lists in c: what its screens read (Valid facts only). -/
def listed (s : Side) (c : Id) : IO (List Id) := do
  return (← (Lists.list (message.all.query [c]) : SqlM Fact (Answer Fact)).run s.db).rows.map (·.1.2)

def main : IO UInt32 := do
  let t ← Checks.new
  let r := room
  let all := r.base ++ r.old ++ r.need ++ r.win
  let shared (l : List Op) := (l.filter fun o => (fam.room o).isSome).map (·.id)
  -- the window: every shared op with no claimed time, or one at the floor or later
  let winIds := shared (all.filter fun o => fam.order o == 0 || floor ≤ fam.order o)
  let below := all.filter fun o => (fam.room o).isSome && fam.order o != 0 && fam.order o < floor
  -- what nothing in the window needs, below the floor, stays behind (the founder's profile, the filler)
  let unneeded := below.filter fun o => !(r.need.any (·.id == o.id))
  -- depth 4: the window and its whole closure, in the window's own flights
  let (flights, b) ← run (sync [r.c] 4) (← side all 0 "a") (← side [] floor "b")
  let got := flights.toList.flatten
  let tw := doneAt flights winIds
  let tc := doneAt flights (winIds ++ shared r.need)
  IO.println s!"windowed sync: the window held after {tw.getD 0} flights, with its closure after {tc.getD 0}; {flights.size} flights in all"
  t.ok "the windowed node ends with the window and its whole closure" tc.isSome
  t.ok "and nothing older that the window does not need" (unneeded.all fun o => !got.contains o.id)
  t.ok "the closure arrives in the window's own flights: one round, no extra round trips" (tc == tw)
  let mut ok := true
  for o in r.win ++ r.need do ok := ok && (← valid b o.id)
  t.ok "every op of the window and its closure is Valid at the windowed node" ok
  -- depth 1: the clump's root, two steps below the reaction, is cut
  let (_, b1) ← run (sync [r.c] 1) (← side all 0 "a") (← side [] floor "b")
  t.ok "depth 1: the child (one step down) arrives" (← holds b1 r.child.id)
  t.ok "depth 1: its clump's root (two steps down) does not" (!(← holds b1 r.root.id))
  t.ok "depth 1: the child stays unjudged, not Valid" (!(← valid b1 r.child.id))
  t.ok "depth 1: so does the reaction on it" (!(← valid b1 r.onChild.id))
  let shown ← listed b1 r.c
  t.ok "depth 1: the child is listed nowhere a screen reads" (!shown.contains r.child.id)
  let mut rest := true
  for o in r.win do
    if o.id != r.onChild.id then rest := rest && (← valid b1 o.id)
  let posts := r.win.filter fun o => match (Codec.decode o.body : Option Body) with | some (.ofPost _) => true | _ => false
  t.ok "depth 1: the rest of the window is Valid, and its messages are listed"
    (rest && posts.all fun o => shown.contains o.id)
  t.finish "windowed sync"

end WindowSync

def main : IO UInt32 := WindowSync.main
