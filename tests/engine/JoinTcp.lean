/-
The join over real TCP on localhost: two nodes, each run by the
engine's runner (`Runner`, Engine/Sync/Tcp.lean) on its own port and
its own SQLite file, with the Connection family's hooks and the Rust
crypto. What a phone does, without the phone.

- A founds Acme and invites at its address; B joins from the link and
  dials A (bare frames).
- Before approval: A opens B's request and answers nothing; B
  establishes nothing.
- A approves: A answers B's next dial; both hold one established
  session (the same id); the first sealed frames carry sync's hello
  and rounds; B ends admitted by its own ops and lets A in.
- A later post streams to B.
- A removes B while their session is live: from then on A sends B none
  of the community's ops (a post of A's does not reach B) and takes
  none of B's (B, not knowing, posts; A does not store it). Each
  connection step reads its rooms afresh (`Node.refresh`), and the
  trust rule refuses B (`rooms_cut`).

Each step is read from the runners' databases through a second
connection (SQLite's WAL lets it read beside the runner's writer).
-/
import tests.engine.Lib
import ops.connection.All

open Engine Engine.Sync Community Tests Connection

def K := sodium
def fam : Family F := node ed25519 K
def cfg : Config := { every := 30000, patience := 20000 }

def fresh (path : String) : IO Db := do
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  Db.openAt path

structure Peer where
  name : String
  seed : ByteArray
  addr : ByteArray
  path : String
  run : Runner

def side (dir name : String) (port : Nat) : IO Peer := do
  let seed := sha256 s!"seed {name}".toUTF8
  let addr := s!"127.0.0.1:{port}".toUTF8
  let path := s!"{dir}/{name}.db"
  let db ← fresh path
  let x : Sync F (SqlM F) := { fam, cfg, hooks := hooks fam K addr }
  let run ← Runner.start x db 0 port.toUInt16
  return { name, seed, addr, path, run }

/-- Read a side's store through a connection of its own. -/
def look {α} (s : Peer) (q : SqlM F α) : IO α := do q.run (← Db.openAt s.path)

def ests (s : Peer) : IO (List Connection.Fact) := do
  return (← look s (rows established.all [] : SqlM F _)).map (·.2)

def allowedOn (s : Peer) (c d : ByteArray) : IO Bool :=
  look s ((Community.allowPeer c d).liftL.run : SqlM F Bool)

def stored (s : Peer) (x : Id) : IO Bool := do return (← look s (Store.getOp x : SqlM F _)).isSome

/-- Wait up to ms for p, checking every 50 ms; how long it took. -/
def waitFor (ms : Nat) (p : IO Bool) : IO (Option Nat) := do
  let t0 ← IO.monoMsNow
  while (← IO.monoMsNow) < t0 + ms do
    if ← p then return some ((← IO.monoMsNow) - t0)
    IO.sleep 50
  return none

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/jointcp"
  IO.FS.createDirAll dir
  let t ← Checks.new
  let base := 47000 + (← IO.monoMsNow) % 900
  let a ← side dir "A" base
  let b ← side dir "B" (base + 1)
  let dA := Device.ofSeed a.seed
  let dB := Device.ofSeed b.seed
  -- A founds and invites at its address; B joins from the link.
  a.run.write (found a.seed "Acme".toUTF8 "Ann".toUTF8 1 (sha256 "key".toUTF8) (sha256 "esk".toUTF8)).ops
  let c := (root dA).id
  let (wi, link) := inviteTo c c dA (sha256 "bearer".toUTF8) [a.addr]
  a.run.write wi.ops
  let req := link.request dB
  b.run.write (joinOps link b.seed "Bea".toUTF8).ops
  -- Before approval.
  let opened ← waitFor 10000 do return (← look a (count opened.all [] : SqlM F _)) ≥ 1
  t.ok "tcp: A opened B's request" opened.isSome
  t.ok "tcp: A stored B's join request" (← stored a req.id)
  IO.sleep 1000
  t.ok "tcp: A answered nothing before approval" ((← ests a).isEmpty)
  t.ok "tcp: B established nothing before approval" ((← ests b).isEmpty)
  t.ok "tcp: B is not admitted on A before approval" (!(← allowedOn a c dB.pk))
  -- A approves.
  let wr ← look a ((approveReq c req.id c dA).liftL.run : SqlM F Community.Write)
  a.run.write wr.ops
  let est ← waitFor 15000 do return (← ests a).length == 1 && (← ests b).length == 1
  t.ok "tcp: each holds one established session" est.isSome
  match ← ests a, ← ests b with
  | [.established ca ..], [.established cb ..] => t.ok "tcp: the same connection id" (ca == cb)
  | _, _ => t.ok "tcp: sessions have the expected shape" false
  -- Sync over the sealed session.
  let admitted ← waitFor 20000 do return (← allowedOn b c dB.pk) && (← allowedOn b c dA.pk)
  t.ok "tcp: B is admitted by its own ops, and lets A in" admitted.isSome
  let p := post c c dA "k".toUTF8 "hello B over TCP".toUTF8 1 5
  a.run.write [p]
  let streamed ← waitFor 10000 (stored b p.id)
  t.ok "tcp: a later post reaches B" streamed.isSome
  IO.println s!"jointcp: opened in {opened}, established in {est}, admitted in {admitted}, post in {streamed} (ms)"
  -- A removes B, on the live session.
  let adms ← look a ((Community.admission.byDevice.read [c, dB.pk]).liftL.run : SqlM F (Answer Community.Fact))
  match adms.rows.head? with
  | none => t.ok "tcp: A holds B's admission" false
  | some ((_, admB), _) =>
    let rm := remove c c c admB dA
    a.run.write [rm]
    let cut ← waitFor 5000 do return !(← allowedOn a c dB.pk)
    t.ok "tcp: A's trust rule refuses B once the removal is held" cut.isSome
    let p2 := post c c dA "k".toUTF8 "after the removal".toUTF8 2 6
    a.run.write [p2]
    let q := post c admB dB "k".toUTF8 "B, not knowing".toUTF8 3 7
    b.run.write [q]
    -- Well past the time the earlier post took to stream.
    IO.sleep 4000
    t.ok "tcp: B posted on its side" (← stored b q.id)
    t.ok "tcp: A's post after the removal does not reach B" (!(← stored b p2.id))
    t.ok "tcp: A does not take B's post" (!(← stored a q.id))
    IO.println s!"jointcp: removal held in {cut} ms; B holds the removal: {← stored b rm.id}; sessions on A: {(← ests a).length}"
  a.run.stop
  b.run.stop
  let code ← t.finish "jointcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
