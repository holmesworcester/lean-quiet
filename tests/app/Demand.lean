/- Real worker/reader races with barriers, not timing-dependent sleeps.
The pool executes the same queue, ticket and publication code as App. -/
import ops.app.Raster
import ops.app.ReaderLife
import tests.engine.Checks

open Engine Community Data Tests

namespace DemandTest

def await (what : String) (condition : IO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then throw (IO.userError s!"timeout: {what}")
    IO.sleep 1

def need (key : Nat) (owner : String := "message") (visible := true) : Demand.Need Nat :=
  ⟨[owner.toUTF8], key, visible⟩

def result (h : Work.Handle Nat Nat) : IO (Option Nat) := do
  await "worker completion" (IO.hasFinished h.result)
  return h.result.get

def queue (ck : Checks) : IO Unit := do
  let pool ← Work.Pool.new (K := Nat) (V := Nat)
  pool.pause true
  let calls ← IO.mkRef (#[] : Array Nat)
  let mut old := #[]
  for i in [0:40] do
    old := old.push (← pool.request (need i) fun _ => do calls.modify (·.push i); return some i)
  let latest ← pool.request (need 100) fun _ => do calls.modify (·.push 100); return some 100
  pool.reconcile [need 100]
  pool.pause false
  ck.ok "fast viewport changes discard every obsolete queued action" ((← result latest) == some 100 && (← calls.get) == #[100])
  let mut retired := true
  for h in old do retired := retired && (← result h).isNone
  ck.ok "retired queued handles finish without waiting for abandoned work" retired
  let stats ← pool.stats
  ck.ok "only the final viewport spends a work step" (stats.steps == 1 && stats.cancelled == 40)

  pool.pause true
  let shared ← pool.request (need 200 "author-a") fun _ => return some 200
  let other ← pool.request (need 200 "author-b") fun _ => return some 999
  pool.reconcile [need 200 "author-b"]
  pool.pause false
  ck.ok "two components share one job and one ticket" (shared.ticket == other.ticket && (← result other) == some 200)
  ck.ok "removing one owner preserves the other owner's result" ((← result shared) == some 200)

  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let steps ← IO.mkRef 0
  let stale ← pool.request (need 300) fun _ => do
    steps.modify (· + 1)
    entered.set true
    await "release old step" release.get
    return none
  await "old work started" entered.get
  pool.reconcile []
  let remount ← pool.request (need 300) fun _ => return some 301
  release.set true
  ck.ok "remount uses a fresh ticket even for the same query key" (remount.ticket != stale.ticket)
  ck.ok "in-flight obsolete continuation runs no second step" ((← result stale).isNone && (← steps.get) == 1)
  ck.ok "remounted component receives its own result" ((← result remount) == some 301)

  pool.pause true
  calls.set #[]
  let slow ← pool.request (need 400 "prefetch" false) fun _ => do calls.modify (·.push 400); return some 400
  let fast ← pool.request (need 401 "picture" true) fun _ => do calls.modify (·.push 401); return some 401
  pool.reconcile [need 400 "prefetch" false, need 401 "picture" true]
  pool.pause false
  discard <| result slow
  discard <| result fast
  ck.ok "visible work runs before earlier prefetch" ((← calls.get) == #[401, 400])

  pool.pause true
  pool.allowBackground false
  calls.set #[]
  let speculative ← pool.request (need 450 "overscan" false) fun _ => do
    calls.modify (·.push 450); return some 450
  let arriving ← pool.request (need 451 "visible" true) fun _ => do
    calls.modify (·.push 451); return some 451
  pool.pause false
  try
    discard <| result arriving
    ck.ok "visible work runs while speculative admission is held for a dependency"
      ((← calls.get) == #[451] && !(← IO.hasFinished speculative.result))
  finally pool.allowBackground true
  discard <| result speculative
  ck.ok "speculation resumes after the visible dependency is delivered" ((← calls.get) == #[451, 450])
  ck.ok "stationary viewport outranks overscan; motion promotes only its predicted viewport"
    (!Raster.urgent 1300 100 0 1000 512 0 && Raster.urgent 1300 100 0 1000 512 200 &&
     !Raster.urgent 1300 100 0 1000 512 (-200) && Raster.urgent 0 100 0 1000 512 200)

  pool.pause true
  calls.set #[]
  let mut hs := #[]
  for i in [500:503] do
    let count ← IO.mkRef 0
    hs := hs.push (← pool.request (need i) fun _ => do
      calls.modify (·.push i)
      count.modify (· + 1)
      return if (← count.get) == 3 then some i else none)
  -- Repeated reconciliations in a different order cannot reset progress
  -- or move established requests behind newer work.
  for _ in [0:20] do pool.reconcile [need 502, need 500, need 501]
  pool.pause false
  for h in hs do discard <| result h
  ck.ok "continuations retain progress and rotate fairly within a class"
    ((← calls.get) == #[500, 501, 502, 500, 501, 502, 500, 501, 502])

def pixels (ck : Checks) : IO Unit := do
  let src : Image.Src := ⟨7, 11, (List.range 77).toArray.map fun i =>
    ((i * 73271).toUInt32 <<< (8 : UInt32)) ||| (80 + i % 176).toUInt32⟩
  for (w, h) in [(1, 1), (3, 5), (19, 27), (31, 4), (4, 31)] do
    for preview in [false, true] do
      let action ← Raster.image (fun _ => some src) w h .light preview
      let mut value := none
      for _ in [0:h + 2] do
        value ← action ()
        if value.isSome then break
      let reference := Image.scaled src w h (Palette.color .light .bg)
      let reference := if preview then Arrival.soften (Palette.color .light .bg) reference else reference
      ck.ok s!"cooperative image equals production scaling {w}x{h} preview={preview}"
        (value.map (·.rows) == some reference.rows)

def reader (ck : Checks) : IO Unit := do
  let db ← openDb ":memory:"
  db.filings
  let c := "reader-cancellation".toUTF8
  for i in [0:40] do
    let f : SF := .inl (.admission c s!"user-{i}".toUTF8 s!"device-{i}".toUTF8 s!"node-{i}".toUTF8)
    (show SqlM SF Unit from do
      Store.setStatus s!"admission-{i}".toUTF8 (.valid f)
      for k in fam.keys f do Store.index k s!"admission-{i}".toUTF8).run db
  let sh ← Reader.Shared.new (← IO.mkRef 1)
  let old := Reader.Want.members c c
  let newest := Reader.Want.people c
  sh.setWants #[old]
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let queries ← IO.mkRef 0
  let initial : Reader.St := { rd := db, afterQuery := fun _ => do
    queries.modify (· + 1)
    if (← queries.get) == 1 then
      entered.set true
      await "reader first query release" release.get }
  let pending ← IO.asTask (prio := .dedicated) ((Reader.pass sh).run initial)
  await "actual first SQLite query" entered.get
  sh.setWants #[newest]
  release.set true
  let (_, state) ← match ← IO.wait pending with
    | .ok s => pure s
    | .error e => throw e
  ck.ok "superseded reader stops at the next query boundary" ((← queries.get) == 1)
  ck.ok "superseded reader cannot publish a partial or obsolete answer" (((← sh.board.get).get? old).isNone)
  let (_, state) ← (Reader.pass sh).run { state with afterQuery := fun _ => pure () }
  ck.ok "latest viewport receives actual SQLite content on the next pass"
    (((← sh.board.get).get? newest).map (·.1) == some (.people 40 true))
  let some ticket := (← sh.plan.get).ticket newest | throw (IO.userError "no current ticket")
  sh.setWants #[]
  sh.setWants #[newest]
  sh.publish ticket (.people 999 false)
  ck.ok "reader publication rejects completion across unmount and remount"
    (((← sh.board.get).get? newest).isNone)
  discard <| (Reader.pass sh).run state
  ck.ok "unmount and remount between passes refills the revoked board answer"
    (((← sh.board.get).get? newest).map (·.1) == some (.people 40 true))

end DemandTest

def main : IO UInt32 := do
  let code ← try
    let ck ← Checks.new
    DemandTest.queue ck
    DemandTest.pixels ck
    DemandTest.reader ck
    ck.finish "component-demand"
  catch e => IO.eprintln s!"component-demand: {e}"; pure 1
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
