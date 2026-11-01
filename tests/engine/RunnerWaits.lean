/- Cancellation of actual public runner calls while its real Node.onTick is
held inside a hook. No alternate event loop or fabricated Runner is used.
The gate is released only after recording the cancellation assertions. -/
import tests.engine.HardenLib

open Engine Engine.Sync Tests

namespace RunnerWaits

def waitFor (ms : Nat) (ready : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← ready then return true
    IO.sleep 1
  return false

structure Blocked where
  runner : Runner
  release : IO.Promise Unit

/-- The first actual timer callback waits at the explicit IO gate. This
keeps both ingress and the write channel stable without faking the runner. -/
def start (crash : Bool := false) : IO Blocked := do
  let db ← Db.openAt ":memory:"
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let armed ← IO.mkRef true
  let x : Sync Nat (SqlM Nat) := {
    fam := Harden.fam
    hooks := {
      rooms := fun _ => pure []
      sealFor := plainSeal
      openFrame := plainOpen
      dial := fun _ => do
        if ← armed.get then
          armed.set false
          entered.resolve ()
          discard <| IO.wait release.result?
          if crash then throw (IO.userError "expected RunnerWaits handler failure")
        pure [] } }
  let runner ← Runner.start x db 0 0 (cfg := { queue := 1 })
  unless ← waitFor 2000 entered.isResolved do
    release.resolve ()
    runner.stop
    throw (IO.userError "runner never reached actual tick gate")
  return ⟨runner, release⟩

/-- Observe the actual lanes request in an otherwise empty capacity-one
control channel, then restore that same request without resolving it. A
retained reply permits failure cleanup after the assertion deadline. -/
def pendingReply (r : Runner) : IO (IO.Promise (List (ByteArray × Nat))) := do
  let full ← waitFor 2000 do
    if ← r.events.trySend (.closed 999999) then
      discard <| r.events.tryRecv
      return false
    return true
  unless full do throw (IO.userError "lanes request did not reach control queue")
  let some (.lanes reply) ← r.events.tryRecv |
    throw (IO.userError "unexpected event in lanes-only fixture")
  unless ← r.events.trySend (.lanes reply) do
    throw (IO.userError "could not restore unanswered lanes request")
  return reply

/-- Both public callers wait against full real channels. Requesting stop
must release them even while the node handler has not returned. -/
def fullQueues (t : Checks) : IO Unit := do
  let b ← start
  let r := b.runner
  let first := Op.make 240 [] "held first local write".toUTF8
  let next := Op.make 240 [] "blocked second local write".toUTF8
  let wrote ← r.writes.trySend [first]
  let controlled ← r.events.trySend (.closed 999999)
  t.ok "wait fixture fills actual write and control channels" (wrote && controlled)
  let writing ← IO.asTask (prio := .dedicated) (r.write [next])
  let querying ← IO.asTask (prio := .dedicated) r.lanes
  IO.sleep 50
  t.ok "full queues backpressure both real public callers before stop"
    (!(← IO.hasFinished writing) && !(← IO.hasFinished querying))
  let stopping ← IO.asTask (prio := .dedicated) r.stop
  let writeDone ← waitFor 500 (IO.hasFinished writing)
  let lanesDone ← waitFor 500 (IO.hasFinished querying)
  t.ok "stop cancels a full-queue Runner.write before handler release" writeDone
  t.ok "stop cancels full-queue Runner.lanes before handler release" lanesDone
  t.ok "external cancellation does not pretend the gated loop has stopped"
    (!(← IO.hasFinished r.done) && !(← IO.hasFinished stopping))
  -- Only now may cleanup make room for a broken SDK-send implementation.
  let retained := match ← r.writes.tryRecv with
    | some [op] => op.id == first.id
    | _ => false
  t.ok "canceled write does not displace already queued local work" retained
  b.release.resolve ()
  let ended ← waitFor 2000 (IO.hasFinished stopping)
  t.ok "actual Runner.stop finishes after the held handler is released" ended
  if ended then discard <| IO.wait stopping
  t.ok "full-queue caller tasks finish after cleanup"
    ((← waitFor 1000 (IO.hasFinished writing)) && (← waitFor 1000 (IO.hasFinished querying)))

/-- A request that was admitted still needs a cancellation path while its
reply remains unanswered. Shutdown is allowed to discard queued requests. -/
def unanswered (t : Checks) : IO Unit := do
  let b ← start
  let r := b.runner
  let querying ← IO.asTask (prio := .dedicated) r.lanes
  let reply ← pendingReply r
  t.ok "actual Runner.lanes waits for its admitted unanswered reply"
    (!(← reply.isResolved) && !(← IO.hasFinished querying))
  let stopping ← IO.asTask (prio := .dedicated) r.stop
  let ended ← waitFor 500 (IO.hasFinished querying)
  t.ok "stop cancels admitted unanswered lanes reply before handler release" ended
  if ended then
    let result ← IO.wait querying
    t.ok "canceled lanes query returns empty" (result.toOption == some [])
  else t.ok "canceled lanes query returns empty" false
  t.ok "lanes cancellation leaves original reply unresolved" (!(← reply.isResolved))
  -- This resolution is cleanup only; it occurs after all reply assertions.
  reply.resolve []
  b.release.resolve ()
  t.ok "unanswered-query fixture stops after cleanup" (← waitFor 2000 (IO.hasFinished stopping))

/-- Channel closure is an independent cancellation signal. In particular,
the SDK's close does not resolve a producer already waiting on a full queue. -/
def closedQueues (t : Checks) : IO Unit := do
  let b ← start
  let r := b.runner
  let first := Op.make 240 [] "closed channel first".toUTF8
  let next := Op.make 240 [] "closed channel blocked".toUTF8
  t.ok "closed-channel fixture fills actual write channel" (← r.writes.trySend [first])
  let writing ← IO.asTask (prio := .dedicated) (r.write [next])
  let querying ← IO.asTask (prio := .dedicated) r.lanes
  let reply ← pendingReply r
  IO.sleep 30
  t.ok "closed-channel fixture starts with blocked callers"
    (!(← IO.hasFinished writing) && !(← IO.hasFinished querying))
  discard <| r.events.close.toBaseIO
  discard <| r.writes.close.toBaseIO
  t.ok "closed channels cancel full-queue Runner.write"
    (← waitFor 500 (IO.hasFinished writing))
  t.ok "closed channels cancel admitted unanswered Runner.lanes"
    (← waitFor 500 (IO.hasFinished querying))
  t.ok "closed-channel cancellation needs neither stop nor runner completion"
    (!(← r.stopped.get) && !(← IO.hasFinished r.done) && !(← reply.isResolved))
  -- Wake an old SDK producer and reply only after recording all assertions.
  discard <| r.writes.tryRecv
  reply.resolve []
  b.release.resolve ()
  r.stop
  t.ok "closed-channel caller tasks finish after cleanup"
    ((← waitFor 1000 (IO.hasFinished writing)) && (← waitFor 1000 (IO.hasFinished querying)))

/-- An actual hook error ends the runner without setting its public stop
flag or closing its queues. The completed task must cancel both waiters. -/
def failedRunner (t : Checks) : IO Unit := do
  let b ← start true
  let r := b.runner
  let first := Op.make 240 [] "failure fixture first".toUTF8
  let next := Op.make 240 [] "failure fixture blocked".toUTF8
  t.ok "failed-runner fixture fills actual write channel" (← r.writes.trySend [first])
  let writing ← IO.asTask (prio := .dedicated) (r.write [next])
  let querying ← IO.asTask (prio := .dedicated) r.lanes
  let reply ← pendingReply r
  IO.sleep 30
  t.ok "runner failure fixture starts with blocked callers"
    (!(← IO.hasFinished writing) && !(← IO.hasFinished querying))
  IO.println "RunnerWaits: the following background handler failure is intentional"
  b.release.resolve ()
  let ended ← waitFor 2000 (IO.hasFinished r.done)
  t.ok "actual failing handler finishes the runner task" ended
  t.ok "failure cancellation is independent of stop flags and closed channels"
    (!(← r.stopped.get) && !(← r.events.isClosed) && !(← r.writes.isClosed))
  t.ok "runner failure cancels full-queue Runner.write"
    (← waitFor 500 (IO.hasFinished writing))
  t.ok "runner failure cancels unanswered Runner.lanes"
    (← waitFor 500 (IO.hasFinished querying))
  reply.resolve []
  discard <| r.writes.tryRecv
  r.stop
  discard <| r.events.close.toBaseIO
  discard <| r.writes.close.toBaseIO
  t.ok "failed-runner caller tasks finish after cleanup"
    ((← waitFor 1000 (IO.hasFinished writing)) && (← waitFor 1000 (IO.hasFinished querying)))

def run (t : Checks) : IO Unit := do
  fullQueues t
  unanswered t
  closedQueues t
  failedRunner t

end RunnerWaits
