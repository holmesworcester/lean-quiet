/- Runner shutdown releases the listener while the Runner is still held.
The native close observation runs without TCP; the real same-port restart
runs where the OS permits listeners. Neither relies on collecting Runner. -/
import tests.engine.HardenLib

open Engine Engine.Sync Tests Harden Std.Async

@[extern "lq_test_listener"] opaque listenerFixture : IO Std.Internal.UV.TCP.Socket
@[extern "lq_test_listener_closed"] opaque closedFixtures : IO UInt32

def localClose (t : Checks) : IO Unit := do
  let native ← listenerFixture
  let ch ← eventChannel {}
  let r : Runner := {
    events := ch, writes := ← Std.CloseableChannel.Sync.new (some 1), port := 0, done := Task.pure (.ok ()), stopped := ← IO.mkRef false,
    listening := Task.pure (.ok ()), slots := ← Std.Mutex.new [],
    listener := native, closing := ← Std.Mutex.new false }
  let held ← IO.mkRef r
  let n ← closedFixtures
  r.stop
  t.ok "stop explicitly closes a retained listener" ((← closedFixtures) == n + 1)
  (← held.get).stop
  t.ok "stop closes the listener exactly once" ((← closedFixtures) == n + 1)

def restart (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  let x := setup .empty false
  let first ← Runner.start x db 0 0
  let held ← IO.mkRef first
  first.stop
  let second ← Runner.start x db 0 first.port
  t.ok "restart rebinds the same port while old Runner is retained" (second.port == first.port)
  (← held.get).stop
  t.ok "stopped runner's channel rejects new writes" (!(← first.writes.trySend []))
  second.stop
  let third ← Runner.start x db 0 first.port
  t.ok "same port restarts a second time" (third.port == first.port)
  third.stop

def main (args : List String) : IO UInt32 := do
  let t ← Checks.new
  try
    localClose t
    if !args.contains "--local" then restart t
  catch e =>
    IO.eprintln s!"runner restart: {e}"
    IO.Process.exit 1
  IO.Process.exit (← t.finish "runner restart").toUInt8
