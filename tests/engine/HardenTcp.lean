/-
Real TCP counterparts of the in-memory Daybreak regressions: stopping
the dialer purges the responder's keys, and excess accepted sockets
receive EOF. Built in the sandbox; run by the lead where loopback works.
-/
import tests.engine.HardenLib

open Engine Engine.Sync Tests Harden Std.Async Std.Net

def main : IO UInt32 := do
  let t ← Checks.new
  let da ← Db.openAt ":memory:"
  let db ← Db.openAt ":memory:"
  seed da; seed db
  let opened ← IO.mkRef (0 : Nat)
  let remote ← IO.mkRef (none : Option ByteArray)
  let xb := setup .empty false
  let xb := { xb with hooks := { xb.hooks with
    openFrame := fun bytes => do
      let frame ← plainOpen bytes
      if frame.isSome then opened.modify (· + 1)
      return frame
    established := do
    let addr ← remote.get
    match addr with
    | none => pure []
    | some addr => (setup addr false).hooks.established } }
  let rb ← Runner.start xb db 0 0
  let xa := setup s!"127.0.0.1:{rb.port}".toUTF8 true
  let ra ← Runner.start xa da 0 0
  remote.set (some s!"127.0.0.1:{ra.port}".toUTF8)
  for _ in [0:200] do
    if (← opened.get) > 0 then break
    IO.sleep 10
  t.ok "TCP peers retain keys while live" (!(← keysGone da) && !(← keysGone db))
  t.ok "TCP peer receives a session frame" ((← opened.get) > 0)
  ra.stop
  let mut gone := false
  for _ in [0:200] do
    if ← keysGone db then
      gone := true
      break
    IO.sleep 10
  t.ok "dialer FIN purges responder keys" gone
  rb.stop
  -- All clients have the same IP; their source ports must not evade the cap.
  let df ← Db.openAt ":memory:"
  let xf := setup .empty false
  let rf ← Runner.start xf df 0 0 (cfg := { queue := 2, maxSocks := 2, perAddr := 10 })
  let mut clients : List TCP.Socket.Client := []
  let closed ← IO.mkRef (0 : Nat)
  for _ in [0:10] do
    let c ← TCP.Socket.Client.mk
    let result ← awaitUv (c.native.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, rf.port⟩))
    match result with
    | .error e => throw e
    | .ok _ => pure ()
    clients := c :: clients
    let _ ← IO.asTask (prio := .dedicated) do
      if let .ok none ← awaitUv (c.native.recv? 1) then closed.modify (· + 1)
  for _ in [0:200] do
    if (← closed.get) ≥ 8 then break
    IO.sleep 10
  t.ok "socket flood closes eight extra accepts" ((← closed.get) == 8)
  t.ok "socket flood retains at most maxSocks" (← rf.slots.atomically do return (← get).length == 2)
  for c in clients do closeSocket c
  rf.stop
  let code ← t.finish "harden_tcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
