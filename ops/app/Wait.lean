/- Bounded lifecycle polling. Only suspend may call waitFor; normal frames
poll completed handles once. A timed-out handle remains owned for a later
poll, so foreground cannot race a still-stopping node. No new axioms. -/
import AppTypes

namespace App

/-- One absolute deadline shared by all teardown stages. The readiness
check must itself be nonblocking. Reserve the last poll interval. -/
def waitFor (deadline : Nat) (ready : M Bool) : M Bool := do
  repeat
    if (← IO.monoMsNow) + 5 ≥ deadline then return false
    if ← ready then return true
    IO.sleep 1

/-- Runs on its own dedicated thread, never on the frame. It retains a
late boot's Runner until stop has closed its listener and sessions. -/
def stopNodes (boot : Option (Task (Except IO.Error Engine.Sync.Runner)))
    (net : Option Engine.Sync.Runner) : IO Unit := do
  if let some r := net then r.stop
  if let some t := boot then
    if let .ok r ← IO.wait t then r.stop

/-- Wiring controls: never called by the app. -/
def waitsOnNode (r : Engine.Sync.Runner) (ops : List Engine.Op) : IO Unit := r.write ops
def waitsOnTask (t : Task Unit) : IO Unit := discard <| IO.wait t
def waitsOnDeadline : M Bool := waitFor 1000 (pure false)

end App
