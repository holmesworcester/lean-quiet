/- Real Runner dial cancellation against a saturated local listener. No
external host/firewall is needed. The listener keeps refusing to accept, so
the OS leaves a real outbound connect pending. -/
import tests.engine.RunnerWaits

open Engine Engine.Sync Tests Std.Async Std.Net

namespace ConnectTcp

structure Blackhole where
  server : TCP.Socket.Server
  retained : List (TCP.Socket.Client × SocketAbort)
  pending : IO.Promise (Except IO.Error Unit)

def Blackhole.new : IO Blackhole := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 1
  let address ← server.getSockName
  let mut retained := []
  for _ in [0:12] do
    let client ← TCP.Socket.Client.mk
    client.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, 0⟩)
    let some cap ← SocketAbort.capture client | throw (IO.userError "backlog client capture")
    let pending ← client.native.connect address
    retained := (client, cap) :: retained
    IO.sleep 30
    if !(← pending.isResolved) then return ⟨server, retained, pending⟩
  discard <| server.getSockName
  throw (IO.userError "loopback listener backlog did not leave a pending connect")

/-- Failure cleanup starts only after lease assertions. Drain the remote
accept queue to let a broken deadline implementation eventually complete. -/
def Blackhole.cleanup (b : Blackhole) (finished : IO Bool) : IO Unit := do
  for (_, cap) in b.retained do discard <| cap.abort
  for _ in [0:1200] do
    if let some peer ← b.server.tryAccept then SocketAbort.closeIdle peer
    if (← b.pending.isResolved) && (← finished) then break
    IO.sleep 10
  for (_, cap) in b.retained do cap.barrier
  discard <| b.server.getSockName

def occupied (r : Runner) : IO Nat := r.slots.atomically do return (← get).length

def courier (label : String) := Op.make 240 [] label.toUTF8

def setup (a b : Op) (first next : ByteArray) : Sync Nat (SqlM Nat) :=
  { fam := Harden.fam, hooks := {
    rooms := fun _ => pure []
    sealFor := plainSeal, openFrame := plainOpen
    outbox := do
      let mut out := []
      for (op, addr) in [(a, first), (b, next)] do
        if (← Store.getOp (F := Nat) op.id).isSome then
          out := out ++ [(op.id, addr, (Msg.hello 0).op.bytes)]
      return out } }

/-- The normal runner creates the pending connection from its stored
courier. The slot is unavailable before timeout, then another actual dial
on the same host succeeds under maxSocks=perAddr=1. -/
def deadline (t : Checks) : IO Unit := do
  let blocked ← Blackhole.new
  let first := (addrText (← blocked.server.getSockName)).toUTF8
  let live ← TCP.Socket.Server.mk
  live.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  live.listen 1
  let next := (addrText (← live.getSockName)).toUTF8
  let a := courier "first blackholed courier"
  let b := courier "next reachable courier"
  let db ← Db.openAt ":memory:"
  (Turn.turn Harden.fam [a] : SqlM Nat Unit).run db
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1, stallMs := 150 }
  let run ← Runner.start (setup a b first next) db 0 0 (cfg := cfg)
  let reserved ← RunnerWaits.waitFor 2000 do return (← occupied run) == 1
  IO.sleep 50
  t.ok "actual Runner reserves its only lease for a blackholed dial"
    (reserved && (← occupied run) == 1)
  let freed ← RunnerWaits.waitFor 2000 do return (← occupied run) == 0
  t.ok "actual Runner connect deadline releases the original native request's lease" freed
  let queued ← run.writes.trySend [b]
  let mut peer := none
  for _ in [0:2000] do
    peer ← live.tryAccept
    if peer.isSome then break
    IO.sleep 1
  t.ok "a subsequent real same-host destination connects after deadline" (queued && peer.isSome)
  if let some accepted := peer then SocketAbort.closeIdle accepted
  let stopping ← IO.asTask (prio := .dedicated) run.stop
  t.ok "runner deadline fixture releases native leases after stop"
    (← RunnerWaits.waitFor 2000 do return (← IO.hasFinished stopping) && (← occupied run) == 0)
  -- Only after the original deadline assertions may the fixture release a
  -- deliberately broken connect. Stop now owns/join this original task.
  blocked.cleanup (do return (← occupied run) == 0)
  unless ← RunnerWaits.waitFor 2000 (IO.hasFinished stopping) do
    throw (IO.userError "deadline fixture cleanup did not finish")

/-- Stop cancels the connect independently of its long configured timeout. -/
def stopped (t : Checks) : IO Unit := do
  let blocked ← Blackhole.new
  let addr := (addrText (← blocked.server.getSockName)).toUTF8
  let a := courier "stop blackholed courier"
  let absent := courier "never queued second courier"
  let db ← Db.openAt ":memory:"
  (Turn.turn Harden.fam [a] : SqlM Nat Unit).run db
  let run ← Runner.start (setup a absent addr addr) db 0 0
    (cfg := { maxSocks := 1, perAddr := 1, stallMs := 30000 })
  let reserved ← RunnerWaits.waitFor 2000 do return (← occupied run) == 1
  IO.sleep 50
  t.ok "stop fixture has a pending actual dial before its long deadline"
    (reserved && (← occupied run) == 1)
  let stopping ← IO.asTask (prio := .dedicated) run.stop
  t.ok "Runner.stop cancels native connect and releases quota without waiting 30 seconds"
    (← RunnerWaits.waitFor 2000 do return (← IO.hasFinished stopping) && (← occupied run) == 0)
  blocked.cleanup (do return (← occupied run) == 0)
  unless ← RunnerWaits.waitFor 2000 (IO.hasFinished stopping) do
    throw (IO.userError "stop fixture cleanup did not finish")
  -- Also lets a disabled-abort negative control finish its cleanup.
  discard <| RunnerWaits.waitFor 3000 do return (← occupied run) == 0

/-- Use an actually refused local TCP endpoint, not malformed address text. -/
def refusedAddress : IO ByteArray := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 1
  let addr := (addrText (← server.getSockName)).toUTF8
  closeListener server.native
  return addr

/-- A completed refused dial transfers the lease into a queued `.dialed
none` event. Stop must release that event even though it was never handled. -/
def queuedFailure (t : Checks) : IO Unit := do
  let b ← RunnerWaits.start
  let run := b.runner
  let addr ← refusedAddress
  let reserved ← run.slots.take {} addr
  let dialing ← IO.asTask (prio := .dedicated)
    (dialOut run.events run.slots addr run.ingress.stopped 150)
  let sent ← RunnerWaits.waitFor 2000 (IO.hasFinished dialing)
  t.ok "real refused dial completion retains lease until queued event is consumed"
    (reserved && sent && (← occupied run) == 1)
  let stopping ← IO.asTask (prio := .dedicated) run.stop
  let sawStop ← RunnerWaits.waitFor 500 run.stopped.get
  b.release.resolve ()
  let ended ← RunnerWaits.waitFor 2000 (IO.hasFinished stopping)
  t.ok "stop drain releases an unhandled failed-dial completion exactly once"
    (sawStop && ended && (← occupied run) == 0)
  if !ended then throw (IO.userError "queued-failure stop did not finish")
  if (← occupied run) != 0 then run.slots.release addr

/-- If a full control queue refuses delivery after stop, the dial task still
owns the lease and must release it itself before the handler gate is freed. -/
def refusedCompletion (t : Checks) : IO Unit := do
  let b ← RunnerWaits.start
  let run := b.runner
  let addr ← refusedAddress
  let reserved ← run.slots.take {} addr
  let full ← run.events.trySend (.closed 999999)
  let dialing ← IO.asTask (prio := .dedicated)
    (dialOut run.events run.slots addr run.ingress.stopped 150)
  IO.sleep 50
  t.ok "refused completion waits behind a full actual control queue"
    (reserved && full && !(← IO.hasFinished dialing) && (← occupied run) == 1)
  let stopping ← IO.asTask (prio := .dedicated) run.stop
  let ended ← RunnerWaits.waitFor 500 (IO.hasFinished dialing)
  t.ok "dial task releases its own lease when stopped completion cannot enqueue"
    (ended && (← occupied run) == 0 && !(← IO.hasFinished run.done))
  b.release.resolve ()
  t.ok "refused-completion fixture stops after cleanup"
    (← RunnerWaits.waitFor 2000 (IO.hasFinished stopping))
  if (← occupied run) != 0 then run.slots.release addr

/-- No capability is the Windows/allocation-failure branch. It must retain
ordinary native connect/send behavior even though cancellation is unavailable. -/
def fallback (t : Checks) : IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 2
  let client ← TCP.Socket.Client.mk
  client.bind (.v4 ⟨IPv4Addr.ofParts 0 0 0 0, 0⟩)
  let connected ← SocketAbort.awaitSend.{0} none 0 (pure true)
    (client.native.connect (← server.getSockName))
  let mut peer := none
  for _ in [0:1000] do
    peer ← server.tryAccept
    if peer.isSome then break
    IO.sleep 1
  let some accepted := peer | throw (IO.userError "fallback accept")
  let payload := "ordinary unsupported-capability IO".toUTF8
  let sent ← SocketAbort.awaitSend.{0} none 0 (pure true) (client.native.send #[payload])
  let mut observed := ByteArray.empty
  while observed.size < payload.size do
    let p ← accepted.native.recv? (payload.size - observed.size).toUInt64
    let some (.ok (some chunk)) ← IO.wait p.result? | break
    if chunk.isEmpty then break
    observed := observed ++ chunk
  t.ok "no-capability fallback preserves ordinary native connect" connected
  t.ok "no-capability fallback preserves ordinary native send" sent
  t.ok "no-capability fallback delivers the actual bytes" (observed == payload)
  SocketAbort.closeIdle client
  SocketAbort.closeIdle accepted

def run (t : Checks) : IO Unit := do
  fallback t
  if !System.Platform.isLinux then
    IO.println "SKIP connect-backlog regression (Linux runner prerequisite)"
    return
  deadline t
  stopped t
  queuedFailure t
  refusedCompletion t

end ConnectTcp
