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

def await (what : String) (ready : IO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← ready) do
    if (← IO.monoMsNow) > deadline then throw (IO.userError s!"timeout: {what}")
    IO.sleep 1

def run (source target : St) (targetSim : Sim) (evict := false) : IO (St × Bool) := do
  let t ← Tests.Checks.new
  let some sender := source.net | return (target, false)
  let some receiver := target.net | return (target, false)
  let some key ← (intentView (Community.currentKey source.me.c)).run' source |
    return (target, false)
  let counter ← IO.mkRef ((← (intentView (Community.topCount source.me.c)).run' source) + 1)
  let futureTime ← IO.mkRef ((← (nowMin).run' source) + 1000000)
  let barriers ← IO.mkRef (#[] : Array (IO.Ref Bool))
  let active ← IO.mkRef true
  let admitted ← IO.mkRef 0
  let sourceWrites := (← sender.counters).writes
  -- Accepted producer batches minus completed actual source write turns:
  -- a conservative count of still queued/in-flight four-op sync jobs.
  let pendingSync : IO Nat := do
    let accepted ← admitted.get
    let completed := ((← sender.counters).writes - sourceWrites).toNat
    return accepted / 4 - completed
  let producer ← IO.asTask (prio := .dedicated) do
    for batch in [0:2048] do
      if !(← active.get) then break
      let mut ops := []
      for j in [0:4] do
        let i := batch * 4 + j
        let body := s!"sync load {i}: ".toUTF8 ++ (⟨Array.replicate 2048 120⟩ : ByteArray)
        let nonce := (sha256 s!"ui-fair/{i}".toUTF8).extract 0 24
        let n ← counter.modifyGet fun n => (n, n + 1)
        ops := ops ++ [sealedPost source.me.c source.me.adm source.me.dev key nonce body n ((← futureTime.get) + i)]
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
    for attempt in [0:(if evict then 1 else 4)] do
      -- Wait for a genuinely new incoming wave before timing each Send.
      -- Fast UI actions can all finish between two transport batches;
      -- that interval alone is not evidence of sustained incoming load.
      -- This setup is outside the unchanged Send-to-paint deadline.
      if !evict then
        let waveEvents := (← receiver.counters).events
        let waveAdmitted ← admitted.get
        for _ in [0:400] do
          target := (← (steps 1).run target).2
          if (← receiver.counters).events > waveEvents && (← admitted.get) > waveAdmitted && (← pendingSync) ≥ 8 then break
          IO.sleep 2
        t.ok s!"a fresh TCP sync wave is active before timed Send {attempt}"
          ((← receiver.counters).events > waveEvents && (← admitted.get) > waveAdmitted)
      t.ok s!"sync producer remains active during write {attempt}" (!(← IO.hasFinished producer))
      if !evict then
        t.ok s!"at least eight accepted sync batches remain queued or in flight at Send {attempt}"
          ((← pendingSync) ≥ 8)
      -- The separate eviction case deliberately establishes a whole newer
      -- page before releasing the raster worker. Its frame bound starts
      -- at release, not at Send. Ordinary latency cases have no barrier.
      let release ← IO.mkRef (!evict)
      barriers.modify (·.push release)
      if evict then
        let entered ← IO.mkRef false
        let some (_, busyRow) := target.rows.toList.head? | throw (IO.userError "busy raster fixture missing")
        let busyBitmap := Row.paint target.font target.dim target.W target.bgRow busyRow.data busyRow.lay none #[]
        let _ ← target.raster.request
          ⟨["fresh-post-flood".toUTF8], .row 0 s!"busy-{attempt}".toUTF8 0 [] target.dim.theme, true⟩ fun _ => do
            unless busyBitmap.rows.size > 0 do throw (IO.userError "empty busy raster fixture")
            entered.set true
            await "newer peer page before first paint" release.get
            return some busyBitmap
        await "finite busy raster started" entered.get
      let text := s!"own write during sync {attempt}"
      let oldIds := target.out.toList.map (·.op.id)
      let counters ← receiver.counters
      let framesBefore ← targetSim.frames.get
      let start ← IO.monoMsNow
      target := (← sendNow.run { target with text }).2
      let some pending := target.out.toList.find? (fun p => !oldIds.contains p.op.id) |
        t.ok s!"Send {attempt} admitted a real signed post" false
        release.set true
        continue
      let id := pending.op.id
      if let .message _ _ _ _ _ n tm _ := pending.fact then
        counter.modify (max · (n + 1))
        futureTime.modify (max · (tm + 1))
      let mut freshCount : Nat := 0
      let mut futurePeer := false
      if evict then
        for _ in [0:400] do
          target := (← (steps 1).run target).2
          let newer ← (intentView (View.read (Community.message.all.query [target.me.c]
            (limit := some 1) (after := some pending.pos)))).run' target
          -- A rows-only answer intentionally elides counts. Request the
          -- actual indexed count separately to establish page eviction.
          let counted ← (intentView (View.read (Community.message.all.query [target.me.c]
            (limit := some 0) (after := some pending.pos)))).run' target
          freshCount := counted.inRange
          let ownTime := match pending.fact with | .message _ _ _ _ _ _ tm _ => tm | _ => 0
          futurePeer := futurePeer || newer.rows.any (fun (_, f) => match f with
            | .message _ user _ _ _ _ tm _ => user == source.me.user && tm > ownTime
            | _ => false)
          if freshCount ≥ half + 8 then break
          IO.sleep 2
        t.ok "a full newer peer page precedes first committed paint"
          (freshCount ≥ half + 8 && futurePeer && target.ownSends.contains id)
      release.set true
      let measureStart ← if evict then IO.monoMsNow else pure start
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
      release.set true
      let elapsed := (← IO.monoMsNow) - measureStart
      t.ok s!"visible native presentation discharges write {attempt}"
        (!target.ownSends.contains id)
      t.ok s!"write {attempt} committed and read back within {frameBound} app frames" committedAt.isSome
      t.ok s!"write {attempt} painted as committed within {frameBound} app frames" displayedAt.isSome
      t.ok s!"write {attempt} reached actual presentation" ((← targetSim.frames.get) > framesBefore)
      if !evict then
        t.ok s!"write {attempt} stays responsive during TCP flood" (elapsed ≤ 1500)
      IO.println s!"ui-fair evict={evict} {attempt}: commit-frame={committedAt}, display-frame={displayedAt}, runner-turns-through-readback={commitTurns}, elapsed-ms={elapsed}, admitted-sync-ops={← admitted.get}, newer-peer-posts={freshCount}"
    t.ok "network service continues between timed local sends"
      ((← receiver.counters).events > eventStart)
    t.ok "sync producer admits new work across the timed local sends"
      ((← admitted.get) > admissionStart)
  finally
    active.set false
    for release in (← barriers.get) do release.set true
  -- The producer uses only trySend and its own bounded retry sleep, so its
  -- stop flag does not wait for a networking channel to drain.
  discard <| IO.wait producer
  let code ← t.finish (if evict then "Visible own send after newer-page eviction (frames measured after raster release)" else "UI priority under real TCP sync")
  return (target, code == 0)

end UiFair
