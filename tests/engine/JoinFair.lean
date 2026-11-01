/- Production TCP/Noise/SQLite regression. A controlled TCP relay delays and
disconnects actual encrypted traffic. Local writes replenish their own bounded
channel from Runner.notify before the next poll, so starvation cannot be hidden
by draining a finite initial queue. This is finite runtime evidence, not a proof
of an infinite fair execution or of native cryptographic security. -/
import tests.engine.Lib
import tests.engine.LoopChecks
import app.connection.Proofs
import app.Commands
import engine.core.Exit

namespace JoinFair
open Engine Engine.Sync Community Tests Connection

def fam : Family F := node ed25519 sodium
def key := Bytes.digest "join-fair/content-key".toUTF8
def seed (name : String) := sha256 s!"join-fair/device/{name}".toUTF8
def nk (name : String) := Bytes.digest s!"join-fair/node/{name}".toUTF8
def device (name : String) := Device.ofSeed (seed name)
def nodeKey (name : String) := cryptoSeal.pub (nk name)

def postAt (c adm : Id) (name : String) (i : Nat) (text : ByteArray) : Op :=
  let nonce := (Bytes.fit 24 (sha256 s!"join-fair/nonce/{name}/{i}".toUTF8))
  sealedPost c adm (device name) key nonce text i (1000 + i)

/-- A targeted fixture for quota ordering. Couriers are read in descending
op-id order, so choose explicit synthetic entropy that places the working
address after all four dead addresses in the actual outgoing row order.
The ordinary scenario still lets the production dial draw its own entropy. -/
def orderedRequest (c : Id) (join : Op) (listen live : ByteArray) (dead : List ByteArray) :
    Option (Op × Op) := Id.run do
  for i in [0:512] do
    let e := sha256 s!"join-fair/adversarial-ephemeral/{i}".toUTF8
    let some ro := Request.op sodium (nk "B") (nodeKey "A") e (hello c listen [join]) | continue
    if dead.all (fun h => bcmp (Send.op live ro).id (Send.op h ro).id == .lt) then
      return some (ro, Eph.op e ro.id)
  return none

structure Peer where
  path : String
  run : Runner

def look {α} (p : Peer) (q : SqlM F α) : IO α := do q.run (← Db.openAt p.path)
def viewOn {α} (p : Peer) (v : View Community.Fact α) : IO α :=
  look p (v.liftL.run : SqlM F α)
def stored (p : Peer) (id : Id) : IO Bool := do
  return (← look p (Store.getOp id : SqlM F _)).isSome
def allowed (p : Peer) (c : Id) (name : String) : IO Bool :=
  viewOn p (allowPeer c (nodeKey name))
def established (p : Peer) : IO Nat := look p (count Connection.established.all [] : SqlM F _)
def sessionIds (p : Peer) : IO (List Id) := do
  return (← look p (rows Connection.established.all [] : SqlM F _)).filterMap fun (_, f) =>
    match f with | .established cid .. => some cid | _ => none
def readable (p : Peer) (id : Id) (expected : ByteArray) : IO Bool := do
  let status ← look p (Store.getStatus id : SqlM F _)
  match status with
  | some (.valid (.inl (.message c _ _ kid text ..))) =>
    return openSealed cryptoSeal c kid text key == some expected
  | _ => return false

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 20
  return false

def firstHintOnly (hint : ByteArray) (h : Hooks F (SqlM F)) : Hooks F (SqlM F) :=
  { h with dial := fun now => do
      return (← h.dial now).filter fun o =>
        match (Codec.decode o.body : Option Connection.Body) with
        | some (.send address) => address == hint
        | _ => true }

def start (dir name : String) (port advertise : Nat)
    (onlyHint : Option ByteArray := none)
    (notify : List Id → IO Unit := fun _ => pure ()) : IO Peer := do
  let path := s!"{dir}/{name}.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  -- The relay address is advertised by the invite. The actual A port is
  -- written for the harness, and every native hook remains the production one.
  let addr := s!"127.0.0.1:{advertise}".toUTF8
  let cfg : Config := { every := 500, askTime := 2000 }
  let h := hooks fam sodium addr
  let h := onlyHint.map (firstHintOnly · h) |>.getD h
  let sync : Sync F (SqlM F) := { fam, cfg, hooks := h }
  let run ← Runner.start sync db 0 port.toUInt16 notify
    (cfg := { tickMs := 40, queue := 8, stallMs := 10000, stopMs := 250 })
  return { path, run }

structure Flood where
  runner : Runner
  c : Id

def dialQueueChecks (t : Checks) : IO Unit := do
  let cfg : RunConfig := { maxSocks := 4, perAddr := 4, maxPending := 8 }
  let hints := (List.range 5).map fun i => s!"127.0.0.1:{48000 + i}".toUTF8
  let (chosen, occupied) := DialQueue.reserve cfg [] hints
  t.ok "actual dial reservation core obeys four-slot host quota" (chosen == hints.take 4 && occupied.length == 4)
  let waiting := hints.filter (!chosen.contains ·)
  let retried := DialQueue.enqueue cfg.maxPending hints[0]! waiting
  t.ok "deferred fifth hint stays ahead of newly retried first hint" (retried == [hints[4]!, hints[0]!])
  let (next, _) := DialQueue.reserve cfg (occupied.drop 1) retried
  t.ok "released quota admits the deferred fifth hint first" (next == [hints[4]!])
  let full := DialQueue.enqueue 1 hints[4]! [hints[0]!]
  t.ok "pending-address capacity rejects without evicting queued work" (full == [hints[0]!])
  let again := DialQueue.enqueue 1 hints[4]! (full.drop 1)
  t.ok "previously rejected address is admitted on retry after capacity frees"
    ((DialQueue.reserve cfg [] again).1 == [hints[4]!])
  let other := "127.0.0.2:48005".toUTF8
  t.ok "a saturated host does not block a different available host"
    ((DialQueue.reserve { cfg with maxSocks := 5 } occupied [hints[4]!, other]).1 == [other])

/-- A transport-domain regression, not a message-size policy. App.sendNow
passes its trimmed draft to this same Community.send intent. The resulting
oversized post verifies locally, and AEAD opens it, but TCP framing rejects
it. Do not publish this poison op into the runners' syncing databases. -/
def frameLimitChecks (t : Checks) (a : Peer) (c cid : Id) : IO Unit := do
  let some (sk, _) ← look a (sessionKeys cid : SqlM F _) |
    t.ok "frame-boundary fixture has actual session keys" false; return
  let text := String.fromUTF8! (⟨Array.replicate (maxFrame + 1) 120⟩ : ByteArray)
  let nonce := (Bytes.fit 24 (sha256 "frame-limit/large-nonce".toUTF8))
  let write ← viewOn a (Community.send c c (device "A") key nonce text.trimAscii.toString.toUTF8 9000)
  let some op := write.ops.head? | t.ok "App send intent returns a post" false; return
  let statuses ← look a (op.reqs.mapM fun id => (Store.getStatus id : SqlM F _))
  let valid := match judge fam op statuses with
    | some (.valid (.inl (.message ..))) => true
    | _ => false
  t.ok "actual App send intent accepts a signed draft above the frame limit"
    (text.utf8ByteSize == maxFrame + 1 && valid)
  let payload := Codec.encode [op.bytes]
  let sealed := Frame.seal sodium cid sk nonce payload
  t.ok "oversized locally valid post still satisfies native AEAD roundtrip"
    (Frame.open sodium sk sealed == some (cid, payload))
  let packet := tagged sealedTag sealed
  let parsed := frames (frame packet)
  t.ok "actual TCP reader rejects oversized encrypted post despite valid signature"
    (packet.size == 74 + payload.size && packet.size > maxFrame && parsed.1.isEmpty && parsed.2.isNone)
  let smallNonce := (Bytes.fit 24 (sha256 "frame-limit/small-nonce".toUTF8))
  let small ← viewOn a (Community.send c c (device "A") key smallNonce "small accepted draft".toUTF8 9001)
  let smallPayload := Codec.encode [small.ops.head!.bytes]
  let smallSealed := Frame.seal sodium cid sk smallNonce smallPayload
  let smallPacket := tagged sealedTag smallSealed
  let accepted := frames (frame smallPacket)
  t.ok "small positive control crosses the same AEAD and TCP frame boundary"
    (accepted.1 == [smallPacket] && accepted.2 == some .empty &&
      Frame.open sodium sk smallSealed == some (cid, smallPayload))
  IO.println s!"frame-limit: draft={text.utf8ByteSize}, op={op.bytes.size}, bundle={payload.size}, encrypted frame={packet.size}, limit={maxFrame}"

def mainBody (args : List String) : IO UInt32 := do
  let dir := args.headD "out/join-fair"
  let relayPort := (args[1]?.getD "0").toNat!
  let aPort := (args[2]?.getD "0").toNat!
  let bPort := (args[3]?.getD "0").toNat!
  let relayBPort := (args[4]?.getD "0").toNat!
  let deadHints := ((args[5]?.getD "").splitOn ",").filterMap fun p =>
    p.toNat?.map fun n => s!"127.0.0.1:{n}".toUTF8
  IO.FS.createDirAll dir
  let t ← Checks.new
  LoopChecks.run t
  dialQueueChecks t
  let active ← IO.mkRef false
  let context ← IO.mkRef (none : Option Flood)
  let made ← IO.mkRef 0
  let committed ← IO.mkRef 0
  let pending ← IO.mkRef ([] : List Id)
  let rejected ← IO.mkRef 0
  let payloadSize ← IO.mkRef 128
  let notify : List Id → IO Unit := fun ids => do
    let own := ids.filter (← pending.get).contains
    pending.modify fun ps => ps.filter (!ids.contains ·)
    committed.modify (· + own.length)
    if (← active.get) && !own.isEmpty then
      if let some f ← context.get then
        let i ← made.modifyGet fun n => (n + 1, n + 1)
        let text : ByteArray := ⟨Array.replicate (← payloadSize.get) (65 + i % 26).toUInt8⟩
        let post := postAt f.c f.c "A" (100 + i) text
        pending.modify (post.id :: ·)
        let accepted ← f.runner.writes.trySend [post]
        unless accepted do
          pending.modify (·.filter (· != post.id))
          rejected.modify (· + 1)
  let a ← start dir "A" aPort relayPort none notify
  let onlyHint := if args.contains "--first-hint-only" then deadHints.head? else none
  let b ← start dir "B" bPort relayBPort onlyHint
  IO.FS.writeFile s!"{dir}/target-port" (toString a.run.port)
  let control (mode : String) : IO Unit := IO.FS.writeFile s!"{dir}/relay-mode" mode
  let finish : IO UInt32 := do
    active.set false
    control "open"
    b.run.stop
    a.run.stop
    let result ← t.finish "join-fair production TCP/Noise/SQLite"
    (← IO.getStdout).flush
    return result
  try
    let c := (root (device "A") (nodeKey "A")).id
    a.run.write (← viewOn a (found (seed "A") "Fair join".toUTF8 "Alice".toUTF8 1 key
      (Bytes.digest "join-fair/esk".toUTF8) (nk "A"))).ops
    t.ok "founder commits through the real runner" (← waitFor 5000 (stored a c))
    t.ok "native runner counts its actual completed local-write turns"
      (← waitFor 1000 do
        let counters ← a.run.counters
        return counters.writes > 0 && counters.completed > 0 &&
          counters.started - counters.completed ≤ 1)
    let hint := s!"127.0.0.1:{relayPort}".toUTF8
    let some (inv, link) ← viewOn a (inviteTo c c (device "A")
        (sha256 "join-fair/bearer".toUTF8) (deadHints ++ [hint]))
      | t.ok "production invite can be composed" false; return ← finish
    a.run.write inv.ops
    let req := link.request (device "B") (nodeKey "B")
    control "pause"
    let joining ← viewOn b (join link (seed "B") "Bob".toUTF8 (nk "B"))
    let mut joinOps := joining.ops
    if args.contains "--ordered-hints" then
      let some (ro, eph) := orderedRequest c req s!"127.0.0.1:{relayBPort}".toUTF8 hint deadHints
        | t.ok "adversarial courier order fixture exists" false; return ← finish
      t.ok "working courier sorts after all four dead-hint couriers"
        (deadHints.all fun h => bcmp (Send.op hint ro).id (Send.op h ro).id == .lt)
      joinOps := joinOps ++ [ro, eph]
    b.run.write joinOps
    IO.sleep 500
    t.ok "delayed actual bare join has not reached founder" (!(← stored a req.id))
    control "open"
    let reached ← waitFor 6000 (stored a req.id)
    t.ok "released bare join reaches founder" reached
    unless reached do return ← finish
    t.ok "join covers every hint beyond dead same-host addresses"
      (link.hints.length == deadHints.length + 1)
    t.ok "neither endpoint establishes before approval"
      ((← established a) == 0 && (← established b) == 0 && !(← allowed a c "B"))
    a.run.write (← viewOn a (approveReq c req.id c (device "A"))).ops
    let admitted ← waitFor 15000 do
      return (← allowed b c "B") && (← allowed b c "A") &&
        (← established a) == 1 && (← established b) == 1
    t.ok "approval bootstraps actual encrypted session and admission" admitted
    unless admitted do return ← finish
    let originalSessions ← sessionIds a
    let adms ← viewOn b (admission.byDevice.read [c, (device "B").pk])
    let some ((_, admB), _) := adms.rows.head?
      | t.ok "joiner has its own admission" false; return ← finish
    if args.contains "--join-only" then
      let post := postAt c admB "B" 1 "post after deferred hint".toUTF8
      b.run.write [post]
      t.ok "deferred-hint join admits a subsequently readable signed post"
        (← waitFor 5000 (readable a post.id "post after deferred hint".toUTF8))
      return ← finish
    frameLimitChecks t a c originalSessions.head!
    context.set (some ⟨a.run, c⟩)
    active.set true
    let initial := postAt c c "A" 1 "start sustained writes".toUTF8
    pending.modify (initial.id :: ·)
    a.run.write [initial]
    t.ok "self-replenishing write source is live" (← waitFor 2000 do return (← committed.get) ≥ 20)
    let before ← committed.get
    let beforeTurns ← a.run.counters
    let marker := postAt c admB "B" 1 "peer event during sustained writes".toUTF8
    b.run.write [marker]
    let delivered ← waitFor 3000 (readable a marker.id "peer event during sustained writes".toUTF8)
    let after ← committed.get
    let afterTurns ← a.run.counters
    let sourceTurns ← b.run.counters
    t.ok "peer marker commits at its actual source while local writes continue"
      (← readable b marker.id "peer event during sustained writes".toUTF8)
    t.ok "peer message progresses while write queue stays nonempty" delivered
    t.ok "writes continue while peer message progresses" (after > before && (← active.get))
    t.ok "write-source continuation never loses its queued refill" ((← rejected.get) == 0)
    IO.println s!"join-fair: peer marker={delivered}; local refill before={before}, after={after}, rejected={← rejected.get}"
    IO.println s!"join-fair: marker turns source={repr sourceTurns}; destination before={repr beforeTurns}, after={repr afterTurns}"
    -- Stop the producer before cleanup, including on the strict-priority
    -- mutant. Thus rejection must be the marker assertion, not a timeout.
    active.set false
    unless delivered do return ← finish
    IO.sleep 150
    control "backpressure-fill"
    payloadSize.set 16384
    active.set true
    -- Announce a real 4 MiB signed/encrypted backlog. One-hot serving can
    -- stay below the relay's steady drain rate. Establish real backpressure
    -- first: the bounded relay stops A→B writes but continues B's wants.
    -- Only its actual read-pause signal and a real runner backlog release
    -- this setup; the original throttled sampling interval stays 2.5 s.
    let large : ByteArray := ⟨Array.replicate 131072 97⟩
    let backlog := (List.range 32).map fun i => postAt c c "A" (100000 + i) large
    pending.modify ((backlog.head!).id :: ·)
    a.run.write backlog
    let filled ← waitFor 10000 do
      let queued := (← a.run.lanes).map (·.2) |>.foldl max 0
      return queued > 0 && (← System.FilePath.pathExists s!"{dir}/backpressure-ready")
    t.ok "finite setup reaches actual relay read pause and runner backlog" filled
    unless filled do return ← finish
    control "backpressure"
    let mut peak := 0
    let began ← IO.monoMsNow
    while (← IO.monoMsNow) < began + 2500 do
      let queued := (← a.run.lanes).map (·.2) |>.foldl max 0
      peak := max peak queued
      IO.sleep 20
    active.set false
    t.ok "throttled encrypted socket develops actual outgoing backlog" (peak > 0)
    t.ok "outgoing backlog respects production socket cap" (peak ≤ 16777216)
    IO.println s!"join-fair: throttled relay outgoing peak={peak} bytes; refill total={← made.get}"
    control "disconnect"
    IO.sleep 250
    control "open"
    let recovered := postAt c c "A" 3 "after disconnect and backpressure".toUTF8
    a.run.write [recovered]
    let resumed ← waitFor 20000 do
      return (← readable b recovered.id "after disconnect and backpressure".toUTF8) &&
        (← established a) == 1 && (← established b) == 1
    t.ok "disconnect reconnects and delivers sealed post" resumed
    t.ok "backpressure/disconnect replaces the original Noise session" ((← sessionIds a) != originalSessions)
    t.ok "reconnect retains joiner's admission and trust"
      ((← allowed a c "B") && (← allowed b c "B") && (← stored b admB))
    t.ok "both native runner tasks remain alive" (!(← IO.hasFinished a.run.done) && !(← IO.hasFinished b.run.done))
    return ← finish
  catch e =>
    IO.eprintln s!"join-fair exception: {e}"
    t.ok "production join/fairness scenario completed without exception" false
    return ← finish

end JoinFair


/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main (args : List String) : IO UInt32 := Engine.exitAfter (JoinFair.mainBody args)
