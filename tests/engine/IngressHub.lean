import engine.wire.IngressIO
import tests.engine.Checks

open Engine.Sync.Ingress

namespace IngressHub

def run (t : Tests.Checks) : IO Unit := do
  let ensure := fun (condition : Bool) (label : String) => t.ok label condition
  let (hub, _) ← Hub.new (α := Nat) 3
  let some a ← hub.reserve | throw (IO.userError "reserve a")
  let some b ← hub.reserve | throw (IO.userError "reserve b")
  let some c ← hub.reserve | throw (IO.userError "reserve c")
  ensure (← hub.reserve).isNone "the fixed peer capacity refuses another source"
  ensure ((← hub.offer b 20) == .accepted) "target has its own mailbox"
  ensure ((← hub.offer b 999) == .full) "a producer cannot overwrite an owed value"
  let mut seen := false
  for _ in [:4] do
    discard <| hub.offer a 10
    discard <| hub.offer c 30
    if (← hub.poll (pure (some 0))) == some 20 then seen := true
  ensure seen "a target is served within four polls under control and peer flood"
  discard <| hub.offer b 21
  let waiting ← IO.asTask (prio := .dedicated) (hub.send b 22)
  IO.sleep 10
  ensure (!(← IO.hasFinished waiting)) "a full mailbox backpressures its own producer"
  hub.retire b
  let started ← IO.monoMsNow
  while !(← IO.hasFinished waiting) && (← IO.monoMsNow) < started + 1000 do IO.sleep 1
  ensure (← IO.hasFinished waiting) "retirement cancels a producer waiting for room"
  ensure (match ← IO.wait waiting with | .ok false => true | _ => false) "cancelled send reports refusal"
  let some replacement ← hub.reserve | throw (IO.userError "replacement reserve")
  ensure (replacement.index == b.index) "retirement frees the bounded slot"
  ensure ((← hub.offer b 666) == .closed) "stale producer cannot populate a recycled slot"
  ensure ((← hub.offer replacement 42) == .accepted) "replacement owns the recycled slot"
  let waitStop ← IO.asTask (prio := .dedicated) (hub.send replacement 43)
  IO.sleep 10
  hub.stop
  let started ← IO.monoMsNow
  while !(← IO.hasFinished waitStop) && (← IO.monoMsNow) < started + 1000 do IO.sleep 1
  ensure (← IO.hasFinished waitStop) "global stop cancels a waiting producer"
  ensure (match ← IO.wait waitStop with | .ok false => true | _ => false) "global cancellation reports refusal"
  ensure ((← hub.offer a 100) == .closed) "stopped hub refuses later offers"
  ensure (← hub.reserve).isNone "stopped hub refuses later reservations"
  ensure (← hub.poll (pure (some 0))).isNone "stopped hub holds no queued values"

end IngressHub
