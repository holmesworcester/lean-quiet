/- Deterministic native regression: the task uses the production StopFlag.
GDB pauses its actual SDK Ref.get between the two exchanges, lets a separate
Lean task request cancellation, then resumes the original read. The request
must survive. The C helper coordinates scheduling only; it never sets the flag. -/
import engine.wire.StopFlag

open Engine.Sync

@[extern "lq_stop_probe_arm"] opaque arm (flag : @& StopFlag) : IO Unit
@[extern "lq_stop_probe_wait"] opaque waitRelease : IO Unit
@[extern "lq_stop_probe_entered"] opaque entered : IO Unit
@[extern "lq_stop_probe_done"] opaque done : IO Unit
@[extern "lq_stop_probe_injected"] opaque injected : IO Bool

def main : IO UInt32 := do
  let flag ← StopFlag.new
  arm flag
  let task ← IO.asTask (prio := .dedicated) do
    waitRelease
    entered
    flag.request
    done
  let before ← flag.get
  let result ← IO.wait task
  let stopped ← flag.get
  let didInject ← injected
  if before || !result.isOk || !stopped || !didInject then
    IO.eprintln s!"FAIL: a completed stop request survives the overlapping old read (before={before}, after={stopped}, injected={didInject})"
    return 1
  flag.request
  unless ← flag.get do
    IO.eprintln "FAIL: repeated stop remains set"
    return 1
  IO.println "stop-flag: deterministic overlapping read/request and repeated stop pass"
  return 0
