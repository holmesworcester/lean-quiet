import engine.renderer.Work

namespace WorkRank

def await (what : String) (condition : IO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then throw (IO.userError s!"timeout: {what}")
    IO.sleep 1

def need (key : Nat) (visible := true) : Demand.Need Nat :=
  ⟨[toString key |>.toUTF8], key, visible⟩

structure Checks where
  passed : IO.Ref Nat
  failed : IO.Ref Nat

def Checks.ok (c : Checks) (name : String) (good : Bool) : IO Unit := do
  if good then c.passed.modify (· + 1)
  else c.failed.modify (· + 1); IO.println s!"FAIL: {name}"

/-- Every completed action can admit a newer visible request. A last-visible
chooser or a prepend-on-admission mutation lets these arrivals overtake T. -/
partial def request (pool : Work.Pool Nat Nat) (calls : IO.Ref (Array Nat))
    (fresh : IO.Ref Nat) (targetBefore : IO.Ref (Option Nat)) (key : Nat)
    (visible := true) : IO (Work.Handle Nat Nat) :=
  pool.request (need key visible) fun _ => do
    calls.modify (·.push key)
    if key == 3 then
      let count := (← pool.stats).completedSelections
      targetBefore.modify fun _ => some count
    let next ← fresh.modifyGet fun n => (n, n + 1)
    if next < 18 then discard <| request pool calls fresh targetBefore next
    return some key

def arrivalRank (c : Checks) : IO Unit := do
  let pool ← Work.Pool.new (K := Nat) (V := Nat)
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let calls ← IO.mkRef (#[] : Array Nat)
  let fresh ← IO.mkRef 6
  let targetBefore ← IO.mkRef (none : Option Nat)
  let blocker ← pool.request (need 99) fun _ => do
    entered.modify fun _ => true
    await "release initial action" release.get
    calls.modify (·.push 99)
    return some 99
  await "initial action started" entered.get
  c.ok "pending action is not a completed selection" ((← pool.stats).completedSelections == 0)
  discard <| request pool calls fresh targetBefore 0
  discard <| request pool calls fresh targetBefore 1 false
  let retired ← request pool calls fresh targetBefore 2 false
  let target ← request pool calls fresh targetBefore 3
  let before ← pool.state.atomically do return ((← get).jobs.map (·.ticket.key))
  c.ok "actual queued predecessors include invisible entries" (before == [0,1,2,3])
  pool.reconcile [need 99, need 0, need 1, need 3]
  discard <| request pool calls fresh targetBefore 4
  discard <| request pool calls fresh targetBefore 5
  c.ok "retirement resolves a queued handle without spending a selection"
    ((← IO.hasFinished retired.result) && retired.result.get == none && (← pool.stats).completedSelections == 0)
  release.modify fun _ => true
  await "target result" (IO.hasFinished target.result)
  await "worker drains continuing arrivals" (pool.state.atomically do return !(← get).running)
  let served ← calls.get
  c.ok "retained target is selected after two predecessors despite continuing arrivals"
    ((← targetBefore.get) == some 3 && served.toList.take 4 == [99,0,1,3])
  c.ok "retained target satisfies initial all-predecessor bound"
    ((← targetBefore.get).any (fun n => n - 1 ≤ 3) && target.result.get == some 3)
  c.ok "new visible arrivals execute without replacing accepted work"
    ((List.range 14 |>.map (· + 4)).all served.contains && served.size == 18)
  let stats ← pool.stats
  c.ok "each finished actual selection is counted once"
    (stats.completedSelections == served.size && stats.steps == served.size && stats.completed == served.size)
  c.ok "retired background entry never executes" (!served.contains 2 && stats.cancelled == 1)
  discard <| IO.wait blocker.result

def outcomes (c : Checks) : IO Unit := do
  let pool ← Work.Pool.new (K := Nat) (V := Nat)
  pool.pause true
  let attempts ← IO.mkRef 0
  let err ← pool.request (need 0) fun _ => throw (IO.userError "intentional rank action failure")
  let continuation ← pool.request (need 1) fun _ => do
    let n ← attempts.modifyGet fun n => (n + 1, n + 1)
    return if n == 3 then some 1 else none
  let fast ← pool.request (need 2) fun _ => return some 2
  c.ok "paused queued work spends no selection" ((← pool.stats).completedSelections == 0)
  pool.pause false
  await "continuation result" (IO.hasFinished continuation.result)
  await "outcome worker drains" (pool.state.atomically do return !(← get).running)
  let stats ← pool.stats
  c.ok "caught action failure reports no value and counts one completed selection"
    ((← IO.hasFinished err.result) && err.result.get == none && stats.cancelled == 1)
  c.ok "continuations and successful actions each count their completed selections"
    (stats.completedSelections == 5 && stats.steps == 5 && stats.completed == 2 &&
      continuation.result.get == some 1 && fast.result.get == some 2)

def cancellationAndPriority (c : Checks) : IO Unit := do
  let pool ← Work.Pool.new (K := Nat) (V := Nat)
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let old ← pool.request (need 7) fun _ => do
    entered.modify fun _ => true
    await "cancelled action release" release.get
    return some 7
  await "cancelled action entered" entered.get
  pool.reconcile []
  release.modify fun _ => true
  await "cancelled action completed" (IO.hasFinished old.result)
  await "cancelled worker idle" (pool.state.atomically do return !(← get).running)
  let stats ← pool.stats
  c.ok "in-flight revoked result is one completed cancelled selection"
    (old.result.get == none && stats.completedSelections == 1 && stats.steps == 1 && stats.cancelled == 1)
  pool.pause true
  let order ← IO.mkRef (#[] : Array Nat)
  let bg ← pool.request (need 8 false) fun _ => do order.modify (·.push 8); return some 8
  let ui ← pool.request (need 9) fun _ => do order.modify (·.push 9); return some 9
  pool.pause false
  await "visible and background work complete" (do return (← IO.hasFinished bg.result) && (← IO.hasFinished ui.result))
  c.ok "visible request precedes an older background request" ((← order.get) == #[9,8])

end WorkRank

def main : IO UInt32 := do
  let c : WorkRank.Checks := ⟨← IO.mkRef 0, ← IO.mkRef 0⟩
  WorkRank.arrivalRank c
  WorkRank.outcomes c
  WorkRank.cancellationAndPriority c
  IO.println s!"work_rank: {← c.passed.get} passed, {← c.failed.get} failed"
  return if (← c.failed.get) == 0 then 0 else 1
