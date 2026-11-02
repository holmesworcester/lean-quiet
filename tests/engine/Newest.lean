/-
Newest first, end to end: a fresh node syncs a 200-message chaos room
(real signed ops from the app's chaos generator: people, messages in many
scripts, reactions, photos with their attachments and 64 KiB chunks) from
a full node, and the order the fresh node stores ops in is checked:

- the structure range (time 0: the root, invitations, admissions...)
  comes first, since everything else needs it;
- then the timed ops newest first; in particular a newer message's photo
  arrives whole before any chunk of an older message's photo.

Times are read from each chunk's own message (its attachment's third
requirement), not from `orderOf`, so a code change that sorts chunks
elsewhere is caught here and not hidden. Two real Nodes, SQLite in
memory, frames delivered in flights (every frame in flight, then the
next): docs/SYNC.md, "Windows and order".
-/
import tests.engine.Lib
import app.Screen

open Engine Engine.Sync Community Tests

namespace Newest

def C := ed25519
def fam := family C

/-- A small picture the chaos generator crops photos from. -/
def src : Image.Src :=
  ⟨96, 64, (List.range (96 * 64)).toArray.map fun i =>
    let x := i % 96
    let y := i / 96
    ((x * 2).toUInt32 <<< 24) ||| ((y * 3).toUInt32 <<< 16) ||| (((x + y) % 256).toUInt32 <<< 8) ||| 255⟩

structure Room where
  c : Id
  base : List Op
  ops : List Op

/-- A founder's community and a chaos room of n messages in it. -/
def room (n : Nat) : Room := Id.run do
  let seed := sha256 "newest founder".toUTF8
  let d := Device.ofSeed seed
  let k := Bytes.digest "newest content key".toUTF8
  let nk := Bytes.digest "newest node key".toUTF8
  let w := (found seed "Newest".toUTF8 "Ann".toUTF8 1 k (Bytes.digest "newest esk".toUTF8) nk).eval DB.empty
  let c := (root d (cryptoSeal.pub nk) (kidOf cryptoSeal k)).id
  let me : Kinds.Accepted.Me := { dev := d, seed, dev_ok := rfl, c, adm := c, user := c, name := "Ann" }
  let jobs := Chaos.make me k #[src] 6 n 0 (Chaos.epoch + 100000)
  return { c, base := w.ops, ops := jobs.toList.flatMap (·.ops) }

def sync (rooms : List Id) : Sync Fact (SqlM Fact) :=
  { fam, cfg := {},
    hooks := { rooms := fun _ => pure (rooms.map .sync), sealFor := plainSeal, openFrame := plainOpen } }

def side (ops : List Op) (addr : String) : IO Side := do
  let db ← Db.openAt ":memory:"
  (receive fam (intake fam true ops)).run db
  return { db, node := Node.boot fam (← (dumpOps (F := Fact)).run db) 0, addr := addr.toUTF8 }

/-- Run a (dialing) and b until b stores nothing new for a few flights:
every frame in flight is delivered, then the next flight; with nothing
in flight, both sides tick. What b stored, in order, and the flights. -/
def run (x : Sync Fact (SqlM Fact)) (a b : Side) (limit : Nat := 400) : IO (List Id × Nat) := do
  let cid := sha256 "newest session".toUTF8
  let (a, ea) ← a.run fun nd => nd.connect x cid "b".toUTF8 true 0
  let (b, eb) ← b.run fun nd => nd.connect x cid "a".toUTF8 false 0
  let mut a := a
  let mut b := b
  let mut toA := payloads eb
  let mut toB := payloads ea
  let mut got : Array Id := #[]
  let mut now := 0
  let mut flights := 0
  let mut idle := 0
  while flights < limit && idle < 5 do
    flights := flights + 1
    now := now + 1000
    let before := got.size
    if toA.isEmpty && toB.isEmpty then
      let (a', e1) ← a.run fun nd => nd.onTick x now
      let (b', e2) ← b.run fun nd => nd.onTick x now
      a := a'; b := b'
      got := got ++ e2.stored.toArray
      toB := payloads e1; toA := payloads e2
    else
      let (fa, fb) := (toA, toB)
      toA := []; toB := []
      for f in fb do
        let (b', e) ← b.run fun nd => nd.onFrame x "a".toUTF8 f now
        b := b'
        got := got ++ e.stored.toArray
        toA := toA ++ payloads e
      for f in fa do
        let (a', e) ← a.run fun nd => nd.onFrame x "b".toUTF8 f now
        a := a'
        toB := toB ++ payloads e
    idle := if got.size == before && toA.isEmpty && toB.isEmpty then idle + 1 else 0
  return (got.toList, flights)

/-- An op's body. -/
def bodyOf (o : Op) : Option Body := Codec.decode o.body

/-- The claimed time of the message a chunk's attachment hangs off, read
from the message itself. -/
def chunkTime (byId : Std.HashMap Id Op) (o : Op) : Option Nat := do
  let .ofChunk _ ← bodyOf o | none
  let att ← byId[o.reqs.getD 1 .empty]?
  let msg ← byId[att.reqs.getD 2 .empty]?
  let .ofPost p ← bodyOf msg | none
  return p.time

/-- The control's room: every chunk as it was before chunks carried their
message's time, claimed at time 0 (Invalid now, but synced all the same). -/
def atZero (ops : List Op) : List Op :=
  ops.map fun o => match bodyOf o with
    | some (.ofChunk b) => mkOp o.reqs (.ofChunk { b with time := 0 })
    | _ => o

/-- Sync the room to a fresh node: what it stored, in order, and the
times of the photos' chunks in that order. -/
def syncRoom (r : Room) (ops : List Op) : IO (List Op × Nat × List Nat × Bool) := do
  let x := sync [r.c]
  let all := r.base ++ ops
  let shared := all.filter fun o => (fam.room o).isSome
  let byId : Std.HashMap Id Op := Std.HashMap.ofList (all.map fun o => (o.id, o))
  let (got, flights) ← run x (← side all "a") (← side [] "b")
  let stored := got.filterMap (byId[·]?)
  return (stored, flights, stored.filterMap (chunkTime byId), shared.all fun o => got.contains o.id)

/-- The chunks' message times never rise: a newer message's photo comes
whole before any chunk of an older one's. -/
def newestPhotos (times : List Nat) : Bool := (times.zip times.tail).all fun (p, q) => q ≤ p

def main : IO UInt32 := do
  let t ← Checks.new
  let r := room 200
  let (ops, flights, times, whole) ← syncRoom r r.ops
  let photos := (times.foldl (fun l tm => if l.contains tm then l else l ++ [tm]) []).length
  IO.println s!"newest: {ops.length} ops stored at the fresh node in {flights} flights; {times.length} chunks of {photos} photos"
  t.ok "the room has photos, several chunks each" (photos ≥ 3 && times.length > photos)
  t.ok "the fresh node ends with every shared op" whole
  -- the structure range first: no timed op before the last untimed one
  let firstTimed := ops.findIdx? fun o => fam.order o != 0
  let lastUntimed := (ops.zipIdx.filter fun (o, _) => fam.order o == 0).getLast?.map (·.2)
  t.ok "structure (time 0) arrives before every timed op"
    (match firstTimed, lastUntimed with | some i, some j => j < i | _, _ => false)
  t.ok "photos arrive newest first: a newer message's chunks all come before an older one's"
    (newestPhotos times)
  let postTimes := ops.filterMap fun o => match bodyOf o with | some (.ofPost p) => some p.time | _ => none
  t.ok "messages arrive newest first" (newestPhotos postTimes)
  -- the control: chunks left at time 0 ride in the structure range, so
  -- they come before every message, and in no order of their messages
  let (ops0, _, times0, whole0) ← syncRoom r (atZero r.ops)
  let firstPost := ops0.findIdx? fun o => match bodyOf o with | some (.ofPost _) => true | _ => false
  let lastChunk := (ops0.zipIdx.filter fun (o, _) => match bodyOf o with
    | some (.ofChunk _) => true | _ => false).getLast?.map (·.2)
  t.ok "control (chunks at time 0): the fresh node still gets them all" whole0
  t.ok "control (chunks at time 0): every chunk comes before every message"
    (match firstPost, lastChunk with | some i, some j => j < i | _, _ => false)
  t.ok "control (chunks at time 0): the photos do not come newest first" (!newestPhotos times0)
  t.finish "newest first"

end Newest

def main : IO UInt32 := Newest.main
