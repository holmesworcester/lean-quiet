/- Production TCP/Noise/SQLite regression. A controlled TCP relay delays and
disconnects actual encrypted traffic. Local writes replenish their own bounded
channel from Runner.notify before the next poll, so starvation cannot be hidden
by draining a finite initial queue. This is finite runtime evidence, not a proof
of an infinite fair execution or of native cryptographic security. -/
import tests.engine.Lib
import ops.connection.All

namespace JoinFair
open Engine Engine.Sync Community Tests Connection

def fam : Family F := node ed25519 sodium
def key := sha256 "join-fair/content-key".toUTF8
def seed (name : String) := sha256 s!"join-fair/device/{name}".toUTF8
def nk (name : String) := sha256 s!"join-fair/node/{name}".toUTF8
def device (name : String) := Device.ofSeed (seed name)
def nodeKey (name : String) := cryptoSeal.pub (nk name)

def postAt (c adm : Id) (name : String) (i : Nat) (text : ByteArray) : Op :=
  let nonce := (sha256 s!"join-fair/nonce/{name}/{i}".toUTF8).extract 0 24
  sealedPost c adm (device name) key nonce text i (1000 + i)

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

def start (dir name : String) (port advertise : Nat)
    (notify : List Id → IO Unit := fun _ => pure ()) : IO Peer := do
  let path := s!"{dir}/{name}.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  -- The relay address is advertised by the invite. The actual A port is
  -- written for the harness, and every native hook remains the production one.
  let addr := s!"127.0.0.1:{advertise}".toUTF8
  let cfg : Config := { every := 500, askTime := 2000 }
  let sync : Sync F (SqlM F) := { fam, cfg, hooks := hooks fam sodium addr }
  let run ← Runner.start sync db 0 port.toUInt16 notify
    (cfg := { tickMs := 40, queue := 8, stallMs := 10000, stopMs := 250 })
  return { path, run }

structure Flood where
  runner : Runner
  c : Id

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/join-fair"
  let relayPort := (args[1]?.getD "0").toNat!
  let aPort := (args[2]?.getD "0").toNat!
  let bPort := (args[3]?.getD "0").toNat!
  let relayBPort := (args[4]?.getD "0").toNat!
  IO.FS.createDirAll dir
  let t ← Checks.new
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
  let a ← start dir "A" aPort relayPort notify
  let b ← start dir "B" bPort relayBPort
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
      (sha256 "join-fair/esk".toUTF8) (nk "A"))).ops
    t.ok "founder commits through the real runner" (← waitFor 5000 (stored a c))
    let hint := s!"127.0.0.1:{relayPort}".toUTF8
    let some (inv, link) ← viewOn a (inviteTo c c (device "A")
        (sha256 "join-fair/bearer".toUTF8) [hint])
      | t.ok "production invite can be composed" false; return ← finish
    a.run.write inv.ops
    let req := link.request (device "B") (nodeKey "B")
    control "pause"
    b.run.write (← viewOn b (join link (seed "B") "Bob".toUTF8 (nk "B"))).ops
    IO.sleep 500
    t.ok "delayed actual bare join has not reached founder" (!(← stored a req.id))
    control "open"
    t.ok "released bare join reaches founder" (← waitFor 10000 (stored a req.id))
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
    context.set (some ⟨a.run, c⟩)
    active.set true
    let initial := postAt c c "A" 1 "start sustained writes".toUTF8
    pending.modify (initial.id :: ·)
    a.run.write [initial]
    t.ok "self-replenishing write source is live" (← waitFor 2000 do return (← committed.get) ≥ 20)
    let before ← committed.get
    let marker := postAt c admB "B" 1 "peer event during sustained writes".toUTF8
    b.run.write [marker]
    let delivered ← waitFor 3000 (readable a marker.id "peer event during sustained writes".toUTF8)
    let after ← committed.get
    t.ok "peer message progresses while write queue stays nonempty" delivered
    t.ok "writes continue while peer message progresses" (after > before && (← active.get))
    t.ok "write-source continuation never loses its queued refill" ((← rejected.get) == 0)
    IO.println s!"join-fair: peer marker={delivered}; local refill before={before}, after={after}, rejected={← rejected.get}"
    -- Stop the producer before cleanup, including on the strict-priority
    -- mutant. Thus rejection must be the marker assertion, not a timeout.
    active.set false
    unless delivered do return ← finish
    IO.sleep 150
    control "backpressure"
    payloadSize.set 16384
    active.set true
    -- Announce a real 4 MiB signed/encrypted backlog. The relay throttles
    -- A→B while allowing B's wants through, so this exercises actual data
    -- backpressure, rather than merely queuing small offer advertisements.
    let large : ByteArray := ⟨Array.replicate 131072 97⟩
    let backlog := (List.range 32).map fun i => postAt c c "A" (100000 + i) large
    pending.modify ((backlog.head!).id :: ·)
    a.run.write backlog
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

def main := JoinFair.main
