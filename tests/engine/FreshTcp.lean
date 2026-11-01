/-
T-fresh over real TCP, through the runner (`Runner`): a peer that never
reads holds up no one else, holds at most its window here, and is
closed once its writer stalls.

Node R holds 64 ops of 512 KiB in one room, and closes a socket whose
writer's write is not done in 1.5 s (`stallMs`). A raw client S opens a
session with R (plain sealing), asks for all of them in eight wants of
4 MiB, one frame each, then 64 more frames each wanting all 64 again,
and never reads: its socket's buffers fill, and R's writer for it
waits. Meanwhile node P syncs the room from R, and R's app writes a
small op.
- P gets all 64 ops: R's loop never waits on S's socket;
- P gets R's write within 2 s of it, with the backlog still flowing
  to P;
- S's lanes at R (`Runner.lanes`, sampled every 20 ms) never hold more
  than the window and one op, however many frames S sends
  (`room_window`): so the cap (`sockCap`) never closes S;
- R closes S's socket within `stallMs` and 1.5 s of S's wants, and not
  before `stallMs`;
- On supported POSIX runtimes S's writer releases its slot without S
  ever reading; Windows retains its existing behavior until a cancellation
  adapter is verified there. The peer can subsequently read to EOF.
Before lanes (`sendOn` in the loop) R's loop stops at S's first full
buffer, and P gets nothing. Serving without the room, or a room blind
to the lanes, fills S's lanes past the window; with no stall deadline
S is never closed (tests/engine/fresh_negative.py).
-/
import tests.engine.HardenLib
import tests.engine.SocketAbort

open Engine Engine.Sync Tests Std.Async Std.Net

namespace FreshTcp

def room : ByteArray := "room".toUTF8

/-- A data op of the room, 512 KiB. -/
def blob (i : Nat) : Op :=
  Op.make 1 [room] (ByteArray.mk (Array.replicate 524288 (i % 251).toUInt8) ++ s!"blob {i}".toUTF8)

/-- A session: a local op, named by tag. -/
def sess (tag : String) : Op := Op.make 200 [] tag.toUTF8

def setup (est : IO.Ref (List (Id × ByteArray × Bool))) : Sync Nat (SqlM Nat) :=
  { fam := Harden.fam, cfg := { every := 1000 }, hooks := {
      rooms := fun _ => pure [.sync room]
      established := est.get
      sealFor := plainSeal, openFrame := plainOpen } }

/-- A session's frame under the plain seal, framed for the socket. -/
def frameOf (cid : Id) (payloads : List ByteArray) : ByteArray :=
  frame (tagged sealedTag (Codec.encode (cid, Codec.encode payloads)))

/-- Gate the actual writer until after protocol retirement. The final
notice must remain queued, then arrive over TCP before EOF. This forces
the race where an asynchronous writer used to discard the notice. -/
def retiredDrain (t : Checks) (full : Bool := false) : IO Unit := do
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  srv.listen 1
  let address ← srv.getSockName
  let peer ← TCP.Socket.Client.mk
  let .ok _ ← awaitUv (peer.native.connect address) | throw (IO.userError "drain client connect")
  let mut accepted := none
  for _ in [0:100] do
    accepted ← srv.tryAccept
    if accepted.isSome then break
    IO.sleep 10
  let some client := accepted | throw (IO.userError "drain server accept")
  let addr := "retired-peer".toUTF8
  let cid := (sess "retired").id
  let db ← Db.openAt ":memory:"
  let x : Sync Nat (SqlM Nat) := { fam := Harden.fam, cfg := {}, hooks := { rooms := fun _ => pure [], sealFor := plainSeal, openFrame := plainOpen } }
  let ch ← eventChannel { queue := 4 }
  let slots : Slots ← Std.Mutex.new []
  let cfg : RunConfig := { sockCap := 4096 }
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  let some input ← ingress.reserve | throw (IO.userError "retired source admission")
  discard <| slots.take cfg addr
  let backlog : List ByteArray := if full then [⟨Array.replicate cfg.sockCap 98⟩] else []
  let out ← Std.Mutex.new ({ lanes := { serve := backlog } } : Outbox)
  let wake ← Std.Condvar.new
  let stopped ← StopFlag.new
  let aborter ← SocketAbort.capture client
  let sock : Sock := { id := 0, client, addr, heard := 0, stopped, out, wake, done := Task.pure (.ok ()), aborter, input := some input }
  let st : RunState := { db, slots, ingress, node := { ix := {}, floor := 0, addrs := [(cid, addr)] }, socks := [sock] }
  let payload := "final removal notice".toUTF8
  let st ← RunState.apply x ch (fun _ => pure ()) cfg st { send := [(addr, payload)], drop := [cid] } 1
  t.ok "retirement removes the socket without waiting for its gated writer" st.socks.isEmpty
  let queued ← sock.lanes
  t.ok s!"retirement retains final notice with ordinary backlog full={full}"
    (queued.urgent == [payload] && queued.serve == backlog)
  let done ← IO.asTask (prio := .dedicated) (writer ch slots 0 client addr out wake 131072 aborter 1500)
  let stop ← StopFlag.new
  let timer ← IO.asTask (prio := .dedicated) do
    for _ in [0:500] do
      if ← IO.hasFinished done then return
      IO.sleep 10
    stop.request
  let mut received := ByteArray.empty
  repeat
    match ← readSocket peer stop 65536 with
    | some b => received := received ++ b
    | none => break
  let expected := (payload :: backlog).foldl (fun bytes p => bytes ++ frame p) ByteArray.empty
  t.ok s!"retired final notice arrives first, before ordinary backlog and EOF, full={full}"
    (received == expected && !(← stop.get))
  discard <| IO.wait done
  discard <| IO.wait timer
  t.ok "drained writer releases its socket slot" (← slots.atomically do return (← get).isEmpty)
  closeSocket peer
  closeListener srv.native

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 2
  return false

def connectedPair : IO (TCP.Socket.Client × TCP.Socket.Client) := do
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  srv.listen 1
  let peer ← TCP.Socket.Client.mk
  let .ok _ ← awaitUv (peer.native.connect (← srv.getSockName)) |
    throw (IO.userError "abort test connect")
  for _ in [0:1000] do
    if let some client ← srv.tryAccept then
      closeListener srv.native
      return (client, peer)
    IO.sleep 2
  throw (IO.userError "abort test accept")

/-- The actual writer must finish and release its actual Slots lease while
the peer never reads and the control channel remains full or closed. Also
cover a retired socket already absent from the main loop's stall scan. -/
def neverReader (t : Checks) (closed retired : Bool) : IO Unit := do
  if System.Platform.isWindows then
    IO.println "SKIP never-reader cancellation: Windows abort adapter not yet verified"
    return
  let tag := s!"closed={closed}, retired={retired}"
  let (client, peer) ← connectedPair
  let some aborter ← SocketAbort.capture client |
    t.ok s!"POSIX writer abort capability exists ({tag})" false; return
  let some peerAborter ← SocketAbort.capture peer |
    t.ok s!"POSIX peer abort capability exists ({tag})" false; return
  let cfg : RunConfig := { queue := 1, maxSocks := 1, perAddr := 1, stallMs := 150 }
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  let some input ← ingress.reserve | throw (IO.userError "never-reader source admission")
  let addr := "never-reader".toUTF8
  let session := sess "never-reader/session"
  let cid := session.id
  let db ← Db.openAt ":memory:"
  (Turn.turn Harden.fam [session] : SqlM Nat Unit).run db
  let x : Sync Nat (SqlM Nat) := { fam := Harden.fam, hooks := {
    rooms := fun _ => pure [], closing := fun _ => pure [cid],
    sealFor := plainSeal, openFrame := plainOpen } }
  let ch ← eventChannel cfg
  discard <| enqueue ch (.frame 999 .empty)
  if closed then discard <| ch.close.toBaseIO
  let slots : Slots ← Std.Mutex.new []
  let taken ← slots.take cfg addr
  let block : ByteArray := ⟨Array.replicate 524288 97⟩
  let out ← Std.Mutex.new ({ lanes := { urgent := List.replicate 32 block } } : Outbox)
  let wake ← Std.Condvar.new
  let stopped ← StopFlag.new
  let sock : Sock := {
    id := 0
    client := client
    addr := addr
    heard := 0
    stopped := stopped
    out := out
    wake := wake
    done := Task.pure (.ok ())
    aborter := some aborter
    input := some input }
  let node : Node := {
    ix := Index.ofOps Harden.fam [session]
    floor := 0
    conns := [(cid, { dialer := false, rooms := [], floor := 0 })]
    addrs := [(cid, addr)] }
  let st : RunState := { db, node, socks := [sock], slots, ingress }
  if retired then
    let (gone, _) ← RunState.close x st 0 1 true
    t.ok s!"retired socket has left the main stall scan ({tag})" gone.socks.isEmpty
  let done ← IO.asTask (prio := .dedicated)
    (writer ch slots 0 client addr out wake cfg.burst (some aborter) cfg.stallMs)
  IO.sleep 50
  let pending ← out.atomically do return (← getThe Outbox).since.isSome
  t.ok s!"actual native writer holds its lease before deadline ({tag})"
    (taken && pending && !(← IO.hasFinished done) && !(← slots.atomically get).isEmpty)
  let finished ← waitFor 2000 (IO.hasFinished done)
  let released := (← slots.atomically get).isEmpty
  t.ok s!"never-reading peer cannot retain writer or slot after deadline ({tag})" (finished && released)
  -- The initial event is removed only AFTER recording completion and lease
  -- assertions. No consumer made room for the writer's closed notification.
  let retained := match ← ch.tryRecv with | some (.frame 999 _) => true | _ => false
  t.ok s!"writer completion did not require consuming full control queue ({tag})" retained
  if !retired then
    let notices ← IO.mkRef ([] : List Id)
    let st := { st with socks := [{ sock with done }] }
    let reaped ← RunState.reap x ch (fun ids => notices.modify (· ++ ids)) cfg st 2000
    t.ok s!"reaper observes actual completion despite lost close notification ({tag})"
      (reaped.socks.isEmpty && reaped.node.conns.isEmpty &&
        (← (Store.getOp cid : SqlM Nat _).run db).isNone && (← notices.get).contains cid)
  let nextAddr := "fresh-peer-after-abort".toUTF8
  let admitted ← slots.take cfg nextAddr
  t.ok s!"released native quota admits a subsequent destination ({tag})" admitted
  if admitted then slots.release nextAddr
  -- Failure cleanup may read, but only after the no-read assertions above.
  -- This lets a deliberately broken abort mutation fail without hanging CI.
  out.atomically (modify fun o => { o with stopped := true, lanes := {} })
  wake.notifyAll
  if !finished then
    let stopRead ← StopFlag.new
    let timer ← IO.asTask (prio := .dedicated) do IO.sleep 2000; stopRead.request
    repeat
      match ← readSocket peer stopRead 65536 with
      | some _ => pure ()
      | none => break
    discard <| IO.wait timer
  discard <| peerAborter.abort
  discard <| aborter.abort
  discard <| waitFor 2000 (IO.hasFinished done)
  discard <| ch.close.toBaseIO

end FreshTcp

open FreshTcp in
def main : IO UInt32 := do
  let t ← Checks.new
  SocketAbortTest.run t
  Harden.wantChecks t
  retiredDrain t
  retiredDrain t true
  neverReader t false false
  neverReader t true false
  neverReader t false true
  let blobs := (List.range 64).map blob
  let sS := sess "stuck"
  let sP := sess "peer"
  let dr ← Db.openAt ":memory:"
  let dp ← Db.openAt ":memory:"
  (Turn.turn Harden.fam ([sS, sP] ++ blobs) : SqlM Nat Unit).run dr
  (Turn.turn Harden.fam [sP] : SqlM Nat Unit).run dp
  let estR ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let estP ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let got ← IO.mkRef ([] : List (Id × Nat))
  let stallMs := 1500
  let rcfg : RunConfig := { stallMs }
  let rr ← Runner.start (setup estR) dr 0 0 (cfg := rcfg)
  let rp ← Runner.start (setup estP) dp 0 0
    (notify := fun ids => do
      let now ← IO.monoMsNow
      got.modify (· ++ ids.map (·, now)))
  -- S: connects to R and never reads.
  let s ← TCP.Socket.Client.mk
  match ← awaitUv (s.native.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, rr.port⟩)) with
  | .error e => throw e
  | .ok _ => pure ()
  let sAddr := addrText (← s.getSockName)
  estR.modify (fun _ => [(sS.id, sAddr.toUTF8, false)])
  -- Sample S's lanes at R: the most they held, and when they went.
  let peak ← IO.mkRef 0
  let seen ← IO.mkRef false
  let gone ← IO.mkRef (none : Option Nat)
  let sampling ← IO.mkRef true
  let sampler ← IO.asTask (prio := .dedicated) do
    while ← sampling.get do
      match (← rr.lanes).find? (·.1 == sAddr.toUTF8) with
      | some (_, b) =>
        seen.modify (fun _ => true)
        peak.modify (max · b)
      | none =>
        if (← seen.get) && (← gone.get).isNone then do
          let when ← IO.monoMsNow
          gone.modify (fun _ => some when)
      IO.sleep 20
  IO.sleep 600
  let ids := blobs.map (·.id)
  let wants := (List.range 8).map fun k => (Msg.want ((blobs.drop (8 * k)).take 8 |>.map (·.id))).op.bytes
  let again := (List.range 64).map fun _ => (Msg.want ids).op.bytes
  let hello := (Msg.hello 0).op.bytes
  let bytes := frameOf sS.id [hello] :: (wants ++ again).map fun w => frameOf sS.id [w]
  match ← awaitUv (s.native.send bytes.toArray) with
  | .error e => throw e
  | .ok _ => pure ()
  let asked ← IO.monoMsNow
  IO.sleep 1000
  -- P syncs from R while R's writer for S waits forever.
  estR.modify (fun _ => [(sS.id, sAddr.toUTF8, false), (sP.id, s!"127.0.0.1:{rp.port}".toUTF8, false)])
  estP.modify (fun _ => [(sP.id, s!"127.0.0.1:{rr.port}".toUTF8, true)])
  let count : IO Nat := do return ((← got.get).filter fun p => ids.contains p.1).length
  for _ in [0:300] do
    if (← count) ≥ 8 then break
    IO.sleep 20
  -- R's app writes while the backlog flows to P.
  let fresh := Op.make 1 [room] "fresh".toUTF8
  let before ← count
  let wrote ← IO.monoMsNow
  rr.write [fresh]
  let mut arrived : Option Nat := none
  for _ in [0:600] do
    if let some (_, at_) := (← got.get).find? (·.1 == fresh.id) then
      arrived := some at_
      break
    IO.sleep 10
  let backlogLeft := 64 - before
  IO.println s!"fresh_tcp: P held {before} of 64 when R wrote; the write arrived in {arrived.map (· - wrote)} ms"
  t.ok "P syncs while S never reads: some of the backlog arrives" (before ≥ 8)
  t.ok "R's write reaches P within 2 s, the backlog still flowing" (arrived.any (· ≤ wrote + 2000) && backlogLeft > 0)
  for _ in [0:1000] do
    if (← count) ≥ 64 then break
    IO.sleep 20
  t.ok "P gets all 64 ops while S never reads" ((← count) == 64)
  for _ in [0:300] do
    if (← gone.get).isSome || (← IO.monoMsNow) > asked + stallMs + 3000 then break
    IO.sleep 20
  let goneAt ← gone.get
  let window := rcfg.window
  IO.println s!"fresh_tcp: S's lanes at R peaked at {← peak.get} B (window {window}); closed {goneAt.map (· - asked)} ms after its wants"
  t.ok "S's lanes stay within the window and one op, whatever S sends" ((← peak.get) ≤ window + 524288 + 65536)
  t.ok "S is not closed before stallMs: the window paces it, the cap never closes it"
    (goneAt.any (· ≥ asked + stallMs))
  t.ok "S is closed within stallMs and 1.5 s of its wants" (goneAt.any (· ≤ asked + stallMs + 1500))
  -- On POSIX, require lease release before allowing S any read. Stop P
  -- first so its connections cannot hide S's lease in the host-only quota.
  if !System.Platform.isWindows then
    rp.stop
    let releasedUnread ← waitFor 3000 do return (← rr.slots.atomically get).isEmpty
    t.ok "S cannot retain its native slot while permanently refusing to read" releasedUnread
  let held := (← rr.slots.atomically get).length
  let stopRead ← StopFlag.new
  let _ ← IO.asTask (prio := .dedicated) do
    IO.sleep 10000
    stopRead.request
  let mut drained := 0
  repeat
    match ← readSocket s stopRead 65536 with
    | some chunk => drained := drained + chunk.size
    | none => break
  let ended := !(← stopRead.get)
  IO.println s!"fresh_tcp: S read {drained} B, then {if ended then "the end" else "nothing more in 10 s"}"
  t.ok "S, once it reads, reads to the socket's end: R's writer shut it down" ended
  if System.Platform.isWindows then
    let mut released := false
    for _ in [0:100] do
      if (← rr.slots.atomically get).length + 1 == held then
        released := true
        break
      IO.sleep 20
    t.ok "Windows legacy writer releases its slot after the peer drains" released
  else
    t.ok "reading after cancellation leaves the native quota empty" (← rr.slots.atomically do return (← get).isEmpty)
  sampling.modify (fun _ => false)
  discard <| IO.wait sampler
  -- A loop stuck on S's socket (the old blocking send) would never stop.
  if (← t.failed.get) == 0 then
    closeSocket s
    rp.stop
    rr.stop
  let code ← t.finish "fresh_tcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
