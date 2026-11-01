/- Write, durable read-back and painted presentation during real TCP sync.
The finite regression measures actual app frames and runner turns. It is
not a theorem giving a wall-clock deadline for arbitrarily delayed native IO.
-/
import Quiet
import platforms.headless.Sim
import tests.engine.Checks

namespace UiFair
open App Engine Community Data

def frameBound : Nat := 64

def run (source target : St) (targetSim : Sim) : IO (St × Bool) := do
  let t ← Tests.Checks.new
  let some sender := source.net | return (target, false)
  let some receiver := target.net | return (target, false)
  let some key ← (intentView (Community.currentKey source.me.c)).run' source |
    return (target, false)
  let active ← IO.mkRef true
  let admitted ← IO.mkRef 0
  let producer ← IO.asTask (prio := .dedicated) do
    for batch in [0:2048] do
      if !(← active.get) then break
      let mut ops := []
      for j in [0:4] do
        let i := batch * 4 + j
        let body := s!"sync load {i}: ".toUTF8 ++ (⟨Array.replicate 2048 120⟩ : ByteArray)
        let nonce := (sha256 s!"ui-fair/{i}".toUTF8).extract 0 24
        -- Older logical positions keep the target's own newly sent post
        -- visible while the sync backlog continues to arrive.
        ops := ops ++ [sealedPost source.me.c source.me.adm source.me.dev key nonce body 1 1]
      repeat
        if !(← active.get) then return
        if ← sender.writes.trySend ops then
          admitted.modify (· + ops.length)
          break
        IO.sleep 1
  let mut target := (← (openPage .chat).run target).2
  try
    -- Require real traffic before measuring the local action.
    let beginning ← receiver.counters
    for _ in [0:400] do
      target := (← (steps 1).run target).2
      if (← admitted.get) ≥ 32 && (← receiver.counters).events > beginning.events then break
      IO.sleep 2
    t.ok "TCP sync traffic is active before local Send"
      ((← admitted.get) ≥ 32 && (← receiver.counters).events > beginning.events)
    let eventStart := (← receiver.counters).events
    let admissionStart ← admitted.get
    for attempt in [0:4] do
      t.ok s!"sync producer remains active during write {attempt}" (!(← IO.hasFinished producer))
      let text := s!"own write during sync {attempt}"
      let oldIds := target.out.toList.map (·.op.id)
      let counters ← receiver.counters
      let framesBefore ← targetSim.frames.get
      let start ← IO.monoMsNow
      target := (← sendNow.run { target with text }).2
      let some pending := target.out.toList.find? (fun p => !oldIds.contains p.op.id) |
        t.ok s!"Send {attempt} admitted a real signed post" false
        continue
      let id := pending.op.id
      let mut committedAt : Option Nat := none
      let mut displayedAt : Option Nat := none
      let mut commitTurns : Nat := 0
      for frameNo in [0:frameBound] do
        target := (← (steps 1).run target).2
        let stored ← (Store.getOp id : SqlM SF _).run target.rd
        if committedAt.isNone && stored == some pending.op then
          committedAt := some (frameNo + 1)
          commitTurns := ((← receiver.counters).completed - counters.completed).toNat
        let (bots, _) := bottoms target
        let visible := (target.ids.findIdx? (fun p => p.2 == id)).any fun i =>
          (target.rows[id]?).any fun row =>
            Raster.near (bots[i]?.getD 0) row.lay.h target.b (viewH target) 0
        let painted := visible && (target.rows[id]?).any fun row =>
          row.data.text == text && !row.data.pending && row.task.isNone &&
          row.painted.1 == row.ver && row.shown.any (fun bitmap =>
            bitmap.rows == (Row.paint target.font target.dim target.W target.bgRow row.data row.lay none #[]).rows)
        if committedAt.isSome && painted then
          displayedAt := some (frameNo + 1)
          break
        IO.sleep 2
      let elapsed := (← IO.monoMsNow) - start
      t.ok s!"write {attempt} committed and read back within {frameBound} app frames" committedAt.isSome
      t.ok s!"write {attempt} painted as committed within {frameBound} app frames" displayedAt.isSome
      t.ok s!"write {attempt} reached actual presentation" ((← targetSim.frames.get) > framesBefore)
      t.ok s!"write {attempt} stays responsive during TCP flood" (elapsed ≤ 1500)
      IO.println s!"ui-fair {attempt}: commit-frame={committedAt}, display-frame={displayedAt}, runner-turns-through-readback={commitTurns}, elapsed-ms={elapsed}, admitted-sync-ops={← admitted.get}"
    t.ok "network service continues while local writes complete"
      ((← receiver.counters).events > eventStart)
    t.ok "sync producer admits new work during the local-write measurements"
      ((← admitted.get) > admissionStart)
  finally
    active.set false
  -- The producer uses only trySend and its own bounded retry sleep, so its
  -- stop flag does not wait for a networking channel to drain.
  discard <| IO.wait producer
  let code ← t.finish "UI priority under real TCP sync"
  return (target, code == 0)

end UiFair
