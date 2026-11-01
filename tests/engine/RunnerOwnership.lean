/- Real accepted-primary / failed-tick ownership regression. The real runner
starts an idle native socket, completes a turn, accepts a second socket, then
its actual due-tick hook throws before Loop.turn can publish that new state. -/
import tests.engine.HardenLib
import tests.engine.SocketAbort

namespace RunnerOwnership
open Engine Engine.Sync Tests Std.Async Std.Net

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 1
  return ← p

def live (hub : Ingress.Hub Event) : IO Nat := hub.registry.atomically do
  return (← getThe (Ingress.Registry Event hub.peers)).live.toArray.filter id |>.size |>.sub 1

def connect (r : Runner) : IO (TCP.Socket.Client × SocketAbort) := do
  let c ← TCP.Socket.Client.mk
  let .ok _ ← awaitUv (c.native.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, r.port⟩)) |
    throw (IO.userError "ownership fixture connect failed")
  let some cap ← SocketAbort.capture c | throw (IO.userError "ownership fixture capture failed")
  return (c, cap)

def run (t : Checks) : IO Unit := do
  let hubRef ← Std.Mutex.new (none : Option (Ingress.Hub Event))
  let armed ← Std.Mutex.new false
  let failedTick ← IO.Promise.new
  let releaseTick ← IO.Promise.new
  let db ← Db.openAt ":memory:"
  let x : Sync Nat (SqlM Nat) := {
    fam := Harden.fam
    hooks := {
      rooms := fun _ => pure []
      sealFor := plainSeal
      openFrame := plainOpen
      dial := fun _ => do
        if ← liftM (armed.atomically (getThe Bool) : IO Bool) then
          if let some hub ← liftM (hubRef.atomically (getThe (Option (Ingress.Hub Event))) : IO (Option (Ingress.Hub Event))) then
            let peers ← live hub
            if peers == 2 then
              failedTick.resolve peers
              discard <| IO.wait releaseTick.result?
              throw (IO.userError "expected RunnerOwnership tick failure")
        pure [] } }
  let r ← Runner.start x db 0 0 (cfg := { tickMs := 0, maxSocks := 4, stallMs := 150, stopMs := 250 })
  hubRef.atomically (set (some r.ingress))
  let (first, firstCap) ← connect r
  unless ← waitFor 2000 (do return (← live r.ingress) == 1) do
    throw (IO.userError "first socket never reached actual addSock")
  let before ← r.counters
  unless ← waitFor 2000 (do return (← r.counters).completed > before.completed) do
    throw (IO.userError "first admitted socket never completed a runner turn")
  t.ok "ownership fixture retains an idle peer from a completed prior turn"
    ((← live r.ingress) == 1 && !(← IO.hasFinished r.done))
  armed.atomically (set true)
  let (second, secondCap) ← connect r
  t.ok "actual accepted primary starts its second socket before the due tick throws"
    ((← waitFor 2000 failedTick.isResolved) && (← IO.wait failedTick.result?) == some 2)
  let (queued, queuedCap) ← connect r
  t.ok "listener owns a third accepted client while the failing tick is held"
    (← waitFor 1000 do return (← r.slots.atomically (getThe (List String))).length == 3)
  releaseTick.resolve ()
  let ended ← waitFor 2000 (IO.hasFinished r.done)
  let original ← if ended then do
    match ← IO.wait r.done with
    | .error e => pure (decide ((e.toString.splitOn "expected RunnerOwnership tick failure").length > 1))
    | _ => pure false
  else pure false
  let counters ← r.counters
  unless original do IO.println "FAIL: runner reports its original tick error without completing the failed turn"
  -- This one assertion is also run with stderr=/dev/full. Its counted failure
  -- must survive the fixture's own failing diagnostic write.
  discard <| (t.ok "runner reports its original tick error without completing the failed turn"
    (ended && original && counters.started == counters.completed + 1)).toBaseIO
  let .ok firstRead ← (first.native.recv? 1).toBaseIO | throw (IO.userError "first peer read registration failed")
  let .ok secondRead ← (second.native.recv? 1).toBaseIO | throw (IO.userError "second peer read registration failed")
  let .ok queuedRead ← (queued.native.recv? 1).toBaseIO | throw (IO.userError "queued peer read registration failed")
  t.ok "loop exception requests native cancellation without waiting for Runner.stop"
    (← waitFor 1000 do return (← r.slots.atomically (getThe (List String))).isEmpty)
  t.ok "failed loop stops the listener and its producers automatically"
    (← waitFor 1000 (IO.hasFinished r.listening))
  let stopping ← IO.asTask (prio := .dedicated) r.stop
  t.ok "Runner.stop returns after an actual failed loop" (← waitFor 2000 (IO.hasFinished stopping))
  t.ok "Runner.stop releases both old and same-turn native socket leases"
    (← waitFor 500 do return (← r.slots.atomically (getThe (List String))).isEmpty)
  let eof (p : IO.Promise (Except IO.Error (Option ByteArray))) : IO Bool := do
    unless ← waitFor 500 p.isResolved do return false
    match ← IO.wait p.result? with
    | some (.ok none) => return true
    | _ => return false
  t.ok "failed-runner stop closes the previously completed peer" (← eof firstRead)
  t.ok "failed-runner stop closes the socket accepted in the failing turn" (← eof secondRead)
  t.ok "automatic cleanup closes an accepted client never admitted by the loop" (← eof queuedRead)
  IO.println s!"runner ownership: counters={repr counters}, leases={(← r.slots.atomically (getThe (List String))).length}, firstEOF={← firstRead.isResolved}, secondEOF={← secondRead.isResolved}"
  (← IO.getStdout).flush
  -- This only closes the external test peers, after ownership assertions.
  discard <| firstCap.abort
  discard <| secondCap.abort
  discard <| queuedCap.abort
  if ← IO.hasFinished stopping then discard <| IO.wait stopping

/-- The actual dial posts completion before its original task is finished.
Hold only that final task continuation; addSock must still retain both jobs. -/
def dialHandoff (t : Checks) : IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 1
  let addr := (addrText (← server.getSockName)).toUTF8
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1, stallMs := 200 }
  let ch ← eventChannel cfg
  let slots : Slots ← Std.Mutex.new []
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  let owners ← JobOwners.new (JobOwners.socketCapacity cfg.maxSocks)
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let reserved ← slots.take cfg addr
  let some dial ← owners.launch (do
    let done ← IO.asTask (prio := .dedicated) do
      dialOut ch slots addr ingress.stopped cfg.stallMs
      entered.resolve ()
      discard <| IO.wait release.result?
    return (done, ⟨pure (), done⟩)) |
      throw (IO.userError "dial ownership fixture admission")
  unless ← waitFor 2000 entered.isResolved do
    release.resolve ()
    throw (IO.userError "dial did not post actual completion")
  let some (.dialed _ (some client)) ← ch.tryRecv |
    throw (IO.userError "actual successful dial completion missing")
  let some peer ← server.tryAccept | throw (IO.userError "dial peer missing")
  closeListener server.native
  let db ← Db.openAt ":memory:"
  let state : RunState := { db, node := Node.boot Harden.fam [] 0, slots, ingress, owners := some owners }
  let (state, sid) ← state.addSock ch cfg client addr 0
  t.ok "actual successful dial handoff admits socket before original dial task completes"
    (reserved && !(← IO.hasFinished dial) && sid.isSome && state.socks.length == 1)
  t.ok "dial and socket retain two original jobs within the configured ownership cap"
    ((← owners.jobs.atomically get).length == 2 && owners.cap == 2)
  ingress.stop
  owners.request
  let joining ← IO.asTask (prio := .dedicated) owners.join
  IO.sleep 25
  t.ok "ownership join cannot forget the original dial task after its completion event"
    (!(← IO.hasFinished joining) && !(← IO.hasFinished dial))
  release.resolve ()
  t.ok "dial handoff cleanup releases original jobs and socket quota"
    ((← waitFor 2000 (IO.hasFinished joining)) && (← slots.atomically get).isEmpty)
  SocketAbort.closeIdle peer

/-- Retiring a socket removes it from RunState but not original job ownership.
Hold the actual writer before its first send; cancellation must preserve drain. -/
def retiring (t : Checks) : IO Unit := do
  let (client, peer) ← SocketAbortTest.pair
  let aborter ← SocketAbort.capture client
  let peerAborter ← SocketAbort.capture peer
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1, stallMs := 150 }
  let ch ← eventChannel cfg
  let slots : Slots ← Std.Mutex.new []
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  let some input ← ingress.reserve | throw (IO.userError "retirement owner source")
  let owners ← JobOwners.new 1
  let addr := "retiring-owner".toUTF8
  let reserved ← slots.take cfg addr
  let release ← IO.Promise.new
  let stopped ← StopFlag.new
  let notice := "last protected retirement notice".toUTF8
  let out ← Std.Mutex.new ({ control := { urgent := [notice] } } : Outbox)
  let wake ← Std.Condvar.new
  let some sock ← owners.launch (do
    let readerDone ← IO.asTask (prio := .dedicated) (reader ingress input 0 client stopped)
    let done ← IO.asTask (prio := .dedicated) do
      discard <| IO.wait release.result?
      writer ch slots 0 client addr out wake cfg.burst aborter cfg.stallMs
        (finishReader stopped client readerDone)
    let s : Sock := {
      id := 0, client, addr, heard := 0, stopped, out, wake, done
      readerDone, aborter, input := some input }
    return (s, ⟨s.cancelOwned ingress, done⟩)) |
      throw (IO.userError "retirement job admission")
  let db ← Db.openAt ":memory:"
  let x := Harden.setup .empty false
  let state : RunState := { db, node := Node.boot Harden.fam [] 0, socks := [sock], slots, ingress, owners := some owners }
  let (gone, _) ← state.close x 0 0 true
  owners.request
  let retained ← out.atomically (getThe Outbox)
  t.ok "failure cancellation retains an already retired notice and its original writer"
    (reserved && gone.socks.isEmpty && retained.draining && !retained.stopped &&
      retained.control.urgent == [notice] && !(← IO.hasFinished sock.done))
  t.ok "retired socket cancellation stops its reader and retires the source immediately"
    ((← stopped.get) && (← input.closed.get))
  let created ← Std.Mutex.new false
  let refused ← owners.launch (do
    created.atomically (set true)
    return ((), ⟨pure (), Task.pure (.ok ())⟩))
  t.ok "full ownership table refuses before creating a new worker"
    (refused.isNone && !(← created.atomically get) && (← owners.jobs.atomically get).length == 1)
  let joining ← IO.asTask (prio := .dedicated) owners.join
  IO.sleep 25
  t.ok "cleanup retains a retired original writer until its native work finishes"
    (!(← IO.hasFinished joining) && !(← IO.hasFinished sock.done))
  -- TCP may split even this small notice. Consume the actual stream through
  -- EOF instead of assuming one recv callback contains the whole frame.
  let receipt ← IO.asTask (prio := .dedicated) do
    let mut bytes := ByteArray.empty
    repeat
      match ← awaitUv (peer.native.recv? 4096) with
      | .ok (some part) => bytes := bytes ++ part
      | _ => break
    return bytes
  release.resolve ()
  let got ← waitFor 1000 (IO.hasFinished receipt)
  let exact ← if got then do
    match ← IO.wait receipt with
    | .ok bytes => pure (bytes == frame notice)
    | _ => pure false
    else pure false
  t.ok "owned retirement still sends the exact final notice before EOF" exact
  t.ok "retired ownership joins only after original writer reader and slot release"
    ((← waitFor 2000 (IO.hasFinished joining)) && (← IO.hasFinished sock.done) &&
      (← IO.hasFinished sock.readerDone) && (← slots.atomically get).isEmpty)
  let next ← owners.launch (do
    return ((), ⟨pure (), Task.pure (.ok ())⟩))
  t.ok "completed original jobs permit safe ownership-table reuse" next.isSome
  owners.join
  if let some cap := peerAborter then discard <| cap.abort

/-- Actual addSock refuses ownership capacity before starting native jobs,
then releases its independently reserved source, client, and socket quota. -/
def refusedSocket (t : Checks) : IO Unit := do
  let (client, peer) ← SocketAbortTest.pair
  let peerAborter ← SocketAbort.capture peer
  let cfg : RunConfig := { maxSocks := 1, perAddr := 1 }
  let slots : Slots ← Std.Mutex.new []
  let addr := "owner-cap-refusal".toUTF8
  let reserved ← slots.take cfg addr
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  let owners ← JobOwners.new 0
  let db ← Db.openAt ":memory:"
  let ch ← eventChannel cfg
  let st : RunState := { db, node := Node.boot Harden.fam [] 0, slots, ingress, owners := some owners }
  let (st, sid) ← st.addSock ch cfg client addr 0
  t.ok "actual addSock refusal releases quota and source without retaining a socket"
    (reserved && sid.isNone && st.socks.isEmpty && (← live ingress) == 0 &&
      (← slots.atomically get).isEmpty && (← owners.jobs.atomically get).isEmpty)
  let .ok receipt ← (peer.native.recv? 1).toBaseIO | throw (IO.userError "refused peer recv")
  let ended ← waitFor 1000 receipt.isResolved
  let eof ← if ended then do
    match ← IO.wait receipt.result? with
    | some (.ok none) => pure true
    | _ => pure false
    else pure false
  t.ok "ownership refusal closes the unstarted native client" eof
  -- Mutant cleanup remains explicit and follows all ownership assertions.
  for sock in st.socks do sock.cancelOwned ingress
  owners.request
  if let some cap := peerAborter then discard <| cap.abort


end RunnerOwnership

def main (args : List String) : IO UInt32 := do
  let t ← Tests.Checks.new
  if args.isEmpty || args.contains "failure" then RunnerOwnership.run t
  if args.isEmpty || args.contains "handoff" then RunnerOwnership.dialHandoff t
  if args.isEmpty || args.contains "retiring" then RunnerOwnership.retiring t
  if args.isEmpty || args.contains "refused" then RunnerOwnership.refusedSocket t
  let code ← t.finish "runner-ownership"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
