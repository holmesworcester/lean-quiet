/-
Event-driven rounds and live answers on two real SQLite nodes, through
the node's actual entry points (`Node.onTick`, `Node.onFrame`,
`Node.onWrite`), ticking every 500 ms, with the production safety
period (engine/sync/EventLaws.lean, RoundRun.lean):

- finding 2's join case: one end shows the room from the start, the
  other stores what admits it mid-session (its rooms on the session
  change then). A round opens and the room's history arrives within a
  few ticks, far inside the safety period. Both ways round: the joiner
  answering (it asks with `hold r []`), and the joiner dialing.
- with no event, no round opens before the safety period;
- a hub mid-round with many peers holds no per-round copy of the room:
  its connections' state is the same for a room of 100 items as of
  4000.
-/
import tests.engine.HardenLib

open Engine Engine.Sync Tests
namespace LiveRounds
open Harden

def room : Id := "room".toUTF8
/-- What admits a node to the room: once stored, its session shows it. -/
def admit : Op := Op.make 7 [] "admission".toUTF8

def history (n : Nat) : List Op := (List.range n).map fun i => Op.make 1 [room] s!"history-{i}".toUTF8

/-- A node whose session shows the room once its admission is stored. -/
def admitted (addr : ByteArray) (dialer : Bool) (cfg : Config) : Sync Nat (SqlM Nat) :=
  let x := setup addr dialer cfg
  { x with hooks := { x.hooks with
      rooms := fun _ => do
        return if (← Store.getOp (F := Nat) admit.id).isSome then [.sync room] else [] } }

structure Net where
  na : Node
  nb : Node
  frames : Array (ByteArray × ByteArray) := #[]
  rbsr : Nat := 0

def a : ByteArray := "live-a".toUTF8
def b : ByteArray := "live-b".toUTF8

/-- Round messages among a frame's payloads. -/
def rounds (bytes : ByteArray) : Nat :=
  match (plainOpen (m := Id) (bytes.extract 1 bytes.size) : Option (Id × ByteArray)) with
  | some (_, bundle) =>
    match (Codec.decode bundle : Option (List ByteArray)) with
    | some ps => (ps.filter fun p => match Op.decode p with
        | some o => match Msg.ofOp o with | some (.rbsr _ _ _) => true | _ => false
        | none => false).length
    | none => 0
  | none => 0

/-- Deliver every frame in flight, and what each delivery sends, until quiet. -/
def settle (xa xb : Sync Nat (SqlM Nat)) (da db : Db) (net : Net) (now : Nat) : IO Net := do
  let mut net := net
  let mut cursor := 0
  while cursor < net.frames.size && cursor < 100000 do
    let (dst, bytes) := net.frames[cursor]!
    cursor := cursor + 1
    net := { net with rbsr := net.rbsr + rounds bytes }
    if dst == a then
      let (n, e) ← (net.na.onFrame xa b bytes now).run da
      net := { net with na := n, frames := net.frames ++ e.send.toArray }
    else
      let (n, e) ← (net.nb.onFrame xb a bytes now).run db
      net := { net with nb := n, frames := net.frames ++ e.send.toArray }
  return { net with frames := #[] }

def tick (xa xb : Sync Nat (SqlM Nat)) (da db : Db) (net : Net) (now : Nat) : IO Net := do
  let (na, ea) ← (net.na.onTick xa now).run da
  let (nb, eb) ← (net.nb.onTick xb now).run db
  settle xa xb da db { net with na, nb, frames := net.frames ++ (ea.send ++ eb.send).toArray } now

def holdsAll (db : Db) (ops : List Op) : IO Bool := do
  let stored := (← (dumpOps (F := Nat)).run db).map (·.id)
  return ops.all fun o => stored.contains o.id

/-- A joins late if `joinerDials`, else B does: the joiner stores its
admission at `late` ms. Returns when the joiner first holds the room's
history (or none), and how many round messages crossed in the quiet
minute after. -/
def join (joinerDials : Bool) (late : Nat := 2000) : IO (Option Nat × Nat × Nat) := do
  let cfg : Config := {}
  let ops := history 40
  let da ← Db.openAt ":memory:"
  let db ← Db.openAt ":memory:"
  seed da; seed db
  -- The member holds the history and its admission; the joiner, nothing.
  let (member, joiner) := if joinerDials then (db, da) else (da, db)
  (Turn.turn fam (admit :: ops) : SqlM Nat Unit).run member
  let xa := admitted b true cfg
  let xb := admitted a false cfg
  let boot := fun (d : Db) => do return Node.boot fam (← (dumpOps (F := Nat)).run d) 0
  let mut net : Net := { na := ← boot da, nb := ← boot db }
  let mut arrived : Option Nat := none
  let mut quiet := 0
  for step in [0:140] do
    let now := step * 500
    if now == late then
      if joinerDials then
        let (n, e) ← (net.na.onWrite xa [admit] now).run da
        net := { net with na := n, frames := net.frames ++ e.send.toArray }
      else
        let (n, e) ← (net.nb.onWrite xb [admit] now).run db
        net := { net with nb := n, frames := net.frames ++ e.send.toArray }
    let before := net.rbsr
    net ← tick xa xb da db net now
    if arrived.isNone && late ≤ now && (← holdsAll joiner ops) then arrived := some (now - late)
    -- 50 s with no event, longer than main's 30 s cadence.
    if late + 20000 ≤ now then quiet := quiet + (net.rbsr - before)
  let roundsTotal := net.rbsr
  return (arrived, quiet, roundsTotal)

/-- The claims a round message carries. -/
def claimsOf (send : List Op) : List Claim :=
  match send.head?.bind Msg.ofOp with
  | some (.rbsr _ _ cs) => cs
  | _ => []

/-- A connection's whole footprint: every set and list it keeps. -/
def footprint (c : Conn) : Nat :=
  c.known.size + c.asked.size + c.offered.size + c.closed.size + c.frontier.length + c.owed.length +
    c.owing.size + c.askTime.size + c.active.length + c.rounded.length + c.epochs.length + c.short.length +
    c.notices.length + c.given.length + c.rooms.length

/-- A hub dialing `peers` peers, each mid-round in a room of n items the
peer holds too, but for one: the hub's connections after the peer's
first answer, with the round still in flight. -/
def hub (n peers : Nat) : List Conn := Id.run do
  let cfg : Config := { params := { leaf := 4, fan := 4 } }
  let items := (List.range n).map fun j => ((⟨j, j⟩ : Key), (toString j).toUTF8)
  let ix : Index := { rooms := [(room, RoomTree.ofList items)] }
  let iy : Index := { rooms := [(room, RoomTree.ofList (items.drop 1))] }
  let mut out := []
  for _ in [0:peers] do
    let hubConn : Conn := { dialer := true, floor := 0, rooms := [room], peerFloor := some 0 }
    let peer : Conn := { dialer := false, floor := 0, rooms := [room] }
    let opened := hubConn.start cfg ix 0
    let reply := peer.onRbsr cfg iy room 1 (claimsOf opened.send) 1
    let back := opened.conn.onRbsr cfg ix room 1 (claimsOf reply.send) 2
    out := back.conn :: out
  return out

end LiveRounds

def main : IO UInt32 := do
  let t ← Checks.new
  let (arrived, quiet, total) ← LiveRounds.join false
  IO.println s!"joining responder: history after {arrived} ms, {quiet} round messages in the quiet 50 s, {total} in all"
  t.ok s!"joining responder: its ask opens a round and the history arrives within 1 s (took {arrived})"
    (arrived.any (· ≤ 1000))
  t.ok s!"joining responder: no round in the quiet 50 s after ({quiet} round messages)" (quiet == 0)
  t.ok s!"joining responder: rounds were exchanged at all ({total})" (total > 0)
  let (arrived, quiet, total) ← LiveRounds.join true
  IO.println s!"joining dialer: history after {arrived} ms, {quiet} round messages in the quiet 50 s, {total} in all"
  t.ok s!"joining dialer: showing the room opens a round and the history arrives within 1 s (took {arrived})"
    (arrived.any (· ≤ 1000))
  t.ok s!"joining dialer: no round in the quiet 50 s after ({quiet} round messages)" (quiet == 0)
  let small := LiveRounds.hub 100 4
  let large := LiveRounds.hub 4000 4
  IO.println s!"hub of 4 peers mid-round: {(small.map LiveRounds.footprint).sum} entries (100 items), {(large.map LiveRounds.footprint).sum} (4000 items)"
  t.ok "hub mid-round: every peer's round is still in flight" (large.all fun c => !c.active.isEmpty)
  t.ok s!"hub mid-round: no per-round copy of the room ({(small.map LiveRounds.footprint).sum} vs {(large.map LiveRounds.footprint).sum} entries for 100 vs 4000 items)"
    ((small.map LiveRounds.footprint) == (large.map LiveRounds.footprint))
  t.finish "live rounds"
