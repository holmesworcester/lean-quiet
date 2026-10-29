/-
An honest room larger than both connection sets, carried by two real
Nodes on SQLite with an in-memory wire. Every observed transition is
checked for bounds and session continuity; later rounds finish deferred asks.
-/
import tests.engine.SyncStats

open Engine Engine.Sync Tests
namespace Harden

def bigSyncChecks (t : Checks) (count := 5000) (cap := 256) : IO Unit := do
  let a := "big-a".toUTF8
  let b := "big-b".toUTF8
  let room := "room".toUTF8
  let ops := (List.range count).map fun i => Op.make 1 [room] s!"big-{i}".toUTF8
  let da ← Db.openAt ":memory:"
  let db ← Db.openAt ":memory:"
  seed da
  seed db
  (Turn.turn fam ops : SqlM Nat Unit).run da
  let cfg : Config := { maxKnown := cap, maxIds := 64, every := 10, askTime := 100, live := 300, retry := 1 }
  let xa := setup b true cfg
  let xb := setup a false cfg
  let (na, ea) ← ((Node.boot fam ops 0).onTick xa 0).run da
  let (nb, eb) ← ((Node.boot fam [] 0).onTick xb 0).run db
  let mut na := na
  let mut nb := nb
  let mut frames := (ea.send ++ eb.send).toArray
  let mut bounded := true
  let mut sameSession := true
  let mut drops := ea.drop.length + eb.drop.length
  let mut peak := 0
  let mut peaks : Peaks := {}
  let mut received := 0
  let mut rounds := 0
  let mut steps := 0
  for round in [0:200] do
    rounds := round + 1
    let now := round * cfg.every
    let mut cursor := 0
    while cursor < frames.size && cursor < 100000 do
      let (dst, bytes) := frames[cursor]!
      cursor := cursor + 1
      let (n, e) ← if dst == a then (na.onFrame xa b bytes now).run da else (nb.onFrame xb a bytes now).run db
      if dst == a then na := n else nb := n
      frames := frames ++ e.send.toArray
      drops := drops + e.drop.length
      steps := steps + 1
      for n in [na, nb] do
        sameSession := sameSession && n.conns.length == 1 && (n.conn? session.id).isSome
        for (_, c) in n.conns do
          peaks := peaks.see c
          peak := max peak (max c.known.size c.asked.size)
          bounded := bounded && c.known.size ≤ cap && c.asked.size ≤ cap && c.askTime.size ≤ cap
    if cursor < frames.size then throw <| IO.userError "big sync failed to quiesce"
    frames := #[]
    received := ((← (dumpOps (F := Nat)).run db).filter (fun o => o.kind == 1)).length
    if received == count then break
    for side in [true, false] do
      let (n, e) ← if side then (na.onTick xa (now + cfg.every)).run da else (nb.onTick xb (now + cfg.every)).run db
      if side then na := n else nb := n
      frames := frames ++ e.send.toArray
      drops := drops + e.drop.length
      sameSession := sameSession && n.conns.length == 1 && (n.conn? session.id).isSome
      for (_, c) in n.conns do
        peaks := peaks.see c
        peak := max peak (max c.known.size c.asked.size)
        bounded := bounded && c.known.size ≤ cap && c.asked.size ≤ cap && c.askTime.size ≤ cap
  let stored := (← (dumpOps (F := Nat)).run db).foldl (fun s o => s.insert o.id) ({} : Std.HashSet Id)
  t.ok "honest big sync delivers every op" (received == count && ops.all fun o => stored.contains o.id)
  t.ok "honest big sync stays in one session without drops" (drops == 0 && sameSession && !(← keysGone da) && !(← keysGone db))
  t.ok "honest big sync bounds sets and timestamps throughout" (bounded && peak == cap)
  t.ok "full round keeps no sender per-op state" (peaks.offered == 0 && peaks.closed == 0 && peaks.frontier == 0 && !peaks.cut)
  IO.println s!"full sync set peaks: {repr peaks}"
  IO.println s!"big sync: {count} ops, cap {cap}, {rounds} rounds, {steps} frames, peak {peak}, drops {drops}"

end Harden
