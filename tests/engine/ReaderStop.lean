/- The actual app reader cancellation helper under a forced SDK Ref.get
interleaving. The unused done task avoids introducing a second reader loop;
GDB pauses this program's actual getter while requestStop tries to publish. -/
import app.Screen
import engine.core.Exit

@[extern "lq_stop_probe_arm_ref"] opaque armRef (ref : @& IO.Ref Bool) : IO Unit
@[extern "lq_stop_probe_wait"] opaque waitRelease : IO Unit
@[extern "lq_stop_probe_entered"] opaque entered : IO Unit
@[extern "lq_stop_probe_done"] opaque done : IO Unit
@[extern "lq_stop_probe_injected"] opaque injected : IO Bool

def mainBody : IO UInt32 := do
  let stopped ← IO.mkRef false
  let worker : Reader.Worker := ⟨stopped, Task.pure (.error (IO.userError "unused reader result"))⟩
  armRef stopped
  let task ← IO.asTask (prio := .dedicated) do
    waitRelease
    entered
    worker.requestStop
    done
  let before ← stopped.get
  let result ← IO.wait task
  let after ← stopped.get
  if before || !result.isOk || !after || !(← injected) then
    IO.eprintln s!"FAIL: the actual reader stop publication survives the overlapping old read (before={before}, after={after})"
    return 1
  worker.requestStop
  unless ← stopped.get do
    IO.eprintln "FAIL: repeated reader cancellation remains published"
    return 1
  IO.println "reader-stop: actual requestStop survives deterministic SDK overlap and repeated cancellation"
  return 0

/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main : IO UInt32 := Engine.exitAfter mainBody
