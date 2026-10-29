/- Boundary and round-snapshot regressions using the actual Conn handlers. -/
import tests.engine.HardenLib

open Engine Engine.Sync Tests
namespace Harden

def bookChecks (t : Checks) : IO Unit := do
  let room := "room".toUTF8
  let o := Op.make 1 [room] "snapshot".toUTF8
  let ix := Index.ofOps fam [o]
  let cfg : Config := { maxKnown := 4, closureCap := 2 }
  let c : Conn := { dialer := false, rooms := [room], floor := 0, peerFloor := some 0 }
  let full := { c.beginRound 1 with peerFloor := some 86400 }
  let served := ((full.onWant fam cfg ix [o.id] : TM Step).run { ops := [o] }).1
  t.ok "full captured range survives a later hello" (served.send == [o] && served.conn.frontier.isEmpty && served.conn.offered.isEmpty)
  let window := ({ c with peerFloor := some 86400 } : Conn).beginRound 1
  let ended := (window.onRbsr cfg ix room 1 [] 1).conn
  let served := (({ ended with peerFloor := some 0 }.onWant fam cfg ix [o.id] : TM Step).run { ops := [o] }).1
  t.ok "window captured range survives its end and later hello" (served.conn.frontier == [room])
  let queued := window.queue cfg [room, room, room]
  t.ok "duplicate requirements use one slot" (queued.frontier == [room] && !queued.closureCut)
  let zero := window.queue { cfg with closureCap := 0 } [room]
  t.ok "zero closure cap cuts explicitly without keeping ids" (zero.frontier.isEmpty && zero.closed.isEmpty && zero.closureCut)
  let cut := window.queue cfg [room, "a".toUTF8, "b".toUTF8]
  let more := cut.queue cfg ["c".toUTF8]
  t.ok "a cut never admits more ids that round" (cut.closureCut && more.closureCut && more.frontier == cut.frontier)
  let fresh := more.beginRound 2
  t.ok "new round resets the closure budget and cut" (fresh.frontier.isEmpty && fresh.closed.isEmpty && !fresh.closureCut)
  let ops := (List.range 40).map fun i => Op.make 1 [room] s!"stream-{i}".toUTF8
  let mut c := c
  let mut bounded := true
  let mut offered := 0
  for o in ops do
    let s := ((c.filed fam cfg [o.id] : TM Step).run { ops := [o] }).1
    offered := offered + (s.send.flatMap fun o => match Msg.ofOp o with | some (.hold _ ids) => ids | _ => []).length
    c := s.conn
    bounded := bounded && c.offered.size ≤ cfg.maxKnown
  t.ok "stream hint is bounded while every fresh op is offered" (bounded && offered == ops.length)
  let first := ops.head!
  let again := ((c.filed fam cfg [first.id] : TM Step).run { ops := [first] }).1
  t.ok "forgotten stream hints permit a repeated have" (!again.send.isEmpty)

end Harden
