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
  -- Two sessions on one socket (a join sent beside an open one): A
  -- retires one, as `kept` does. The socket and the other session stay
  -- up, and its frames still flow; the socket's end then ends both on B.
  -- B opens both at the address of A's socket as B accepted it, so B
  -- never dials A: with a second socket, each session's address would
  -- follow its last frame (`Node.setAddr`), and retiring one could close
  -- the other's socket (1 run in 100 failed "still flow" so).
  let da2 ← Db.openAt ":memory:"
  let db2 ← Db.openAt ":memory:"
  seed da2; seed2 da2; seed db2; seed2 db2
  let fast : Config := { every := 200 }
  let retire ← IO.mkRef false
  let remote2 ← IO.mkRef (none : Option ByteArray)
  let seen2 ← IO.mkRef (0 : Nat)
  let xb2 := setup .empty false fast
  let xb2 := { xb2 with hooks := { xb2.hooks with
    closing := fun cid => pure [cid]
    openFrame := fun bytes => do
      let frame ← plainOpen bytes
      if let some (cid, _) := frame then
        if cid == session2.id then seen2.modify (· + 1)
      return frame
    established := do
      match ← remote2.get with
      | none => pure []
      | some addr => pure [(session.id, addr, false), (session2.id, addr, false)] } }
  let rb2 ← Runner.start xb2 db2 0 0
  let addrB := s!"127.0.0.1:{rb2.port}".toUTF8
  let xa2 := setup addrB true fast
  let xa2 := { xa2 with hooks := { xa2.hooks with
    closing := fun cid => pure [cid]
    established := do
      let kept := [(session2.id, addrB, true)]
      return if ← retire.get then kept else (session.id, addrB, true) :: kept } }
  let ra2 ← Runner.start xa2 da2 0 0
  for _ in [0:300] do
    if let some (a, _) := (← rb2.lanes).head? then
      remote2.set (some a)
      break
    IO.sleep 10
  t.ok "A's one socket reaches B" (← remote2.get).isSome
  for _ in [0:300] do
    if (← seen2.get) > 0 then break
    IO.sleep 10
  t.ok "two sessions share one socket" ((← seen2.get) > 0)
  retire.set true
  for _ in [0:300] do
    if ← keysGone da2 then break
    IO.sleep 10
  t.ok "retiring one session of a shared socket purges its keys" (← keysGone da2)
  let before ← seen2.get
  let mut flowed := false
  for _ in [0:300] do
    if (← seen2.get) > before then
      flowed := true
      break
    IO.sleep 10
  t.ok "the other session's frames still flow on the shared socket" flowed
  t.ok "the other session keeps its keys on both ends" (!(← keysGone2 da2) && !(← keysGone2 db2))
  ra2.stop
  let mut ended := false
  for _ in [0:300] do
    if (← keysGone db2) && (← keysGone2 db2) then
      ended := true
      break
    IO.sleep 10
  t.ok "the shared socket's EOF ends every session on it" ended
  rb2.stop
  let code ← t.finish "harden_tcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
