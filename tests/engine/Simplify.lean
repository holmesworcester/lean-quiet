/-
Sync simplification regressions on the running Conn and Node. Two SQLite
nodes tick at different cadences with delayed frames; room progress,
secrecy, terminal sessions and purge notifications use their actual paths.
-/
import tests.engine.HardenLib

open Engine Engine.Sync Tests
namespace Simplify
open Harden

def offered (ops : List Op) : List Id := ops.flatMap fun o =>
  match Msg.ofOp o with | some (.hold _ ids) => ids | _ => []

def clock (t : Checks) : IO Unit := do
  let cfg : Config := { live := 30, every := 1000, askTime := 20 }
  let c := (Conn.open false [] 0 0).conn
  let tick := fun c now => ((c.tick fam cfg {} now : TM Step).run {}).1
  t.ok "open enters Hello" (c.session == .hello)
  t.ok "keepalive is not early" ((tick c 9).send.isEmpty)
  t.ok "quiet tick emits empty have at live/3" ((tick c 10).send.map Op.bytes == [(Msg.hold .empty []).op.bytes])
  t.ok "both roles pulse even with no rooms" (((tick { c with dialer := true } 10).send.map Op.bytes) == [(Msg.hold .empty []).op.bytes])
  let hello := ((c.recv fam cfg {} (Msg.hello 0).op.bytes 1 : TM Step).run {}).1
  t.ok "responder answers hello after the dialer has keys" (hello.send.map Op.bytes == [(Msg.hello c.floor).op.bytes])
  let c := hello.conn
  t.ok "peer hello enters Live" (c.session == .live)
  t.ok "deadline is inclusive" (!(tick c 31).drop)
  let closed := tick c 32
  t.ok "silence enters Closed" (closed.drop && closed.conn.session == .closed)
  let replay := ((closed.conn.recv fam cfg {} (Msg.hello 0).op.bytes 33 : TM Step).run {}).1
  t.ok "a replayed hello cannot reopen Closed" (replay.conn.session == .closed)

def pair (t : Checks) : IO Unit := do
  let da ← Db.openAt ":memory:"
  let db ← Db.openAt ":memory:"
  seed da; seed db
  let cfg : Config := { live := 30, every := 1000, askTime := 20 }
  let xa := { setup "b".toUTF8 true cfg with hooks := { (setup "b".toUTF8 true cfg).hooks with rooms := fun _ => pure [] } }
  let xb := { setup "a".toUTF8 false cfg with hooks := { (setup "a".toUTF8 false cfg).hooks with rooms := fun _ => pure [] } }
  let mut a := Node.boot fam [] 0
  let mut b := Node.boot fam [] 0
  let mut flight : List (Nat × Bool × ByteArray) := []
  let mut drops := 0
  let mut frames := 0
  for now in [0:601] do
    for (_, fromA, bytes) in flight.filter (fun p => p.1 ≤ now) do
      if fromA then
        let (n, e) ← (b.onFrame xb "a".toUTF8 bytes now).run db
        b := n; drops := drops + e.drop.length
        for (_, bytes) in e.send do flight := flight ++ [(now + 10, false, bytes)]; frames := frames + 1
      else
        let (n, e) ← (a.onFrame xa "b".toUTF8 bytes now).run da
        a := n; drops := drops + e.drop.length
        for (_, bytes) in e.send do flight := flight ++ [(now + 10, true, bytes)]; frames := frames + 1
    flight := flight.filter (fun p => now < p.1)
    if now % 10 == 0 then
      let (n, e) ← (a.onTick xa now).run da
      a := n; drops := drops + e.drop.length
      for (_, bytes) in e.send do flight := flight ++ [(now + 10, true, bytes)]; frames := frames + 1
    if now % 7 == 0 then
      let (n, e) ← (b.onTick xb now).run db
      b := n; drops := drops + e.drop.length
      for (_, bytes) in e.send do flight := flight ++ [(now + 10, false, bytes)]; frames := frames + 1
  t.ok "delayed keepalives keep both SQLite sessions live" (drops == 0 && frames > 60 &&
    (a.conn? session.id).any (·.session == .live) && (b.conn? session.id).any (·.session == .live))
  t.ok "node records outgoing time" ((a.conn? session.id).any (·.sent == 600))
  t.ok "live sessions retain keys" (!(← keysGone da) && !(← keysGone db))
  let some c := a.conn? session.id | t.ok "live pair still connected" false; return
  let (edge, atEdge) ← (a.onTick xa (c.heard + cfg.live)).run da
  t.ok "node stays open at silence boundary" (atEdge.drop.isEmpty)
  let (ended, afterEdge) ← (edge.onTick xa (c.heard + cfg.live + 1)).run da
  t.ok "silent peer drops and notifies purge" ((ended.conn? session.id).isNone &&
    afterEdge.drop.contains session.id && afterEdge.purged.contains session.id && (← keysGone da))

def rooms (t : Checks) : IO Unit := do
  let slow := "slow".toUTF8
  let fast := "fast".toUTF8
  let cfg : Config := { every := 10 }
  let c : Conn := { dialer := true, rooms := [slow, fast], floor := 0, peerFloor := some 0, snaps := [((slow, 1), [])], round := 1 }
  let s := ((c.tick fam cfg {} 10 : TM Step).run {}).1
  let rounds := s.send.filterMap fun o => match Msg.ofOp o with | some (.rbsr r _ _) => some r | _ => none
  t.ok "a stalled room does not gate another room" (rounds == [fast] && s.conn.snaps.any (·.1 == (slow, 1)))
  let denied := c.onRbsr cfg {} "unshown".toUTF8 7 [.ids ⟨⟨0, 0⟩, none⟩ []] 11
  t.ok "unshown room gets empty end" (denied.send.map Op.bytes == [(Msg.rbsr "unshown".toUTF8 7 []).op.bytes])
  t.ok "unshown room cannot drop or change another round" (!denied.drop && denied.conn.snaps == c.snaps && denied.conn.round == c.round)
  let ended := s.conn.onRbsr cfg {} fast s.conn.round [] 11
  let next := ((ended.conn.tick fam cfg {} 20 : TM Step).run {}).1
  t.ok "completed room starts again beside stalled room" (next.send.any fun o => match Msg.ofOp o with | some (.rbsr r _ _) => r == fast | _ => false)

def secrecy (t : Checks) : IO Unit := do
  let r := "room".toUTF8
  let shared := Op.make 1 [r] "shared".toUTF8
  let outside := Op.make 1 ["other".toUTF8] "outside".toUTF8
  let pending := Op.make 1 [r] "not committed".toUTF8
  let ids := [shared.id, outside.id, key1.id, pending.id]
  let c : Conn := { dialer := false, rooms := [r], floor := 2, roundFloor := 2, frontier := ids }
  let h : Trace := { ops := [shared, outside, key1] }
  let s := ((c.filed fam {} ids : TM Step).run h).1
  t.ok "filed advertises only stored shared room ops" (offered s.send == [shared.id])
  let (d, pairs) := ((c.walk fam {} : TM _).run h).1
  t.ok "closure advertises only stored shared room ops" (pairs.map (·.2) == [shared.id] && d.frontier.isEmpty)
  let cfg : Config := { maxKnown := 0 }
  let s := c.onRbsr cfg {} r 2 [.ids ⟨⟨0, 0⟩, none⟩ [pending.id]] 1
  t.ok "handler itself caps asks without a clamp" (s.conn.asked.isEmpty)

def notices (t : Checks) : IO Unit := do
  let r := "room".toUTF8
  let x := Op.make 1 [r] "removal notice".toUTF8
  let c := ((Conn.open false [r] 0 0).conn).carry [.notice r x.id]
  let st : Trace := { ops := [x] }
  let g := ((c.tickGive fam { live := 30 } {} 10 : TM Step).run st).1
  t.ok "typed notice cuts sync while giving the removal" (c.rooms.isEmpty &&
    g.send.any (·.id == x.id) && g.given == [x.id])
  t.ok "notice delivery preserves phase and silence clock" (g.conn.session == c.session &&
    g.conn.heard == c.heard && !g.drop)
  let again := ((g.conn.filedGive fam {} [x.id] : TM Step).run st).1
  t.ok "filed after tick never repeats a given notice" (again.given.isEmpty && again.send.isEmpty)
  let dropped := ((g.conn.tickGive fam { live := 30 } {} 31 : TM Step).run st).1
  t.ok "notice wrapper expires strictly on silence" (dropped.drop && dropped.conn.session == .closed &&
    dropped.send.isEmpty && dropped.given.isEmpty)

def purges (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  seed db
  let courier := Op.make 243 [] "shipped".toUTF8
  (Turn.turn fam [courier] : SqlM Nat Unit).run db
  let x := setup "peer".toUTF8 false
  let (n, _) ← ((Node.boot fam [] 0).onTick x 0).run db
  let x := { x with hooks := { x.hooks with outbox := pure [(courier.id, "invalid".toUTF8, courier.bytes)] } }
  let (_, e) ← (n.onClose x "peer".toUTF8 1).run db
  t.ok "courier and session purges both reach Effects" (e.purged.contains courier.id && e.purged.contains session.id && (← keysGone db))
  let seen ← IO.mkRef ([] : List Id)
  let ch ← eventChannel {}
  let slots ← Std.Mutex.new []
  let st : RunState := { db, node := Node.boot fam [] 0, slots }
  discard <| st.apply x ch (fun ids => seen.modify (· ++ ids)) {} { purged := e.purged } 1
  t.ok "TCP apply notifies purges without a store write" ((← seen.get) == e.purged)

end Simplify

def main : IO UInt32 := do
  let t ← Checks.new
  Simplify.clock t
  Simplify.pair t
  Simplify.rooms t
  Simplify.secrecy t
  Simplify.notices t
  Simplify.purges t
  t.finish "simplify"
