/-
A send never waits on sync: App.submit offers a write to the node's
bounded inbound channel with `offerAll` (trySend), and what does not fit
waits in the app, offered again first each frame. Here, over a real
bounded channel kept full (as peers' frames keep it while the node is
slow): the offer returns at once, keeps every write in order, and takes
exactly as many as there is room for; and, the negative control, the
blocking send Runner.write uses waits on the same full channel.

    nodequeue
-/
import Quiet

open App Engine

def main : IO UInt32 := do
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    if !ok then fails.modify (· + 1)
  let ch ← Std.CloseableChannel.Sync.new (α := Engine.Sync.Event) (some 2)
  -- full: the peers' frames got there first
  let _ ← ch.trySend .stop
  let _ ← ch.trySend .stop
  let o1 := Op.make 0 [] "1".toUTF8
  let o2 := Op.make 0 [] "2".toUTF8
  let o3 := Op.make 0 [] "3".toUTF8
  let q := #[[o1], [o2], [o3]]
  let t0 ← IO.monoMsNow
  let rest ← offerAll ch q
  let t1 ← IO.monoMsNow
  check s!"a full channel: the offer returns at once ({t1 - t0} ms) and keeps every write" (t1 - t0 < 50 && rest.size == 3)
  -- one slot frees: exactly the first write goes in, the rest stay, in order
  let _ ← ch.tryRecv
  let rest ← offerAll ch rest
  check s!"one slot free: the first goes in, the others stay in order ({rest.size} left)"
    (rest.size == 2 && (rest.map fun w => w.map (·.id)) == #[[o2.id], [o3.id]])
  -- the negative control: the blocking send waits while the channel is full
  let t ← IO.asTask (prio := .dedicated) (Engine.Sync.enqueue ch (.write [o2]))
  IO.sleep 200
  check "control: the blocking send (Runner.write's) is still waiting on the full channel" !(← IO.hasFinished t)
  -- release it
  let _ ← ch.tryRecv
  let _ ← ch.tryRecv
  let _ ← IO.wait t
  return if (← fails.get) == 0 then 0 else 1
