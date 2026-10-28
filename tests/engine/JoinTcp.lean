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
- Each node handshakes with its own key: the sessions name node keys,
  never device keys (docs/REMOVAL.md, E3).
- A removes B while their session is live: from then on A sends B none
  of the community's ops (a post of A's does not reach B) and takes
  none of B's (B, not knowing, posts; A does not store it). Each
  connection step reads its rooms afresh (`Node.refresh`), and the
  trust rule refuses B's node (`rooms_cut`).
- The bare path takes only a join: the removed B dials A with a fresh
  post in its hello. A opens the request, stores neither the post nor
  anything for it, and answers nothing (`bare_takes_only_join`,
  `answer_trusted`). Negative control: the deliver step as it was
  before the fix, run on A's database, takes the post.
- A rejoin is dialed beside an open session: A and B also share a
  second community, so their one session stays open after the removal.
  B, holding its removal, joins again as a new device; its request goes
  bare beside the session, A approves it, and B is let in again
  (`rejoin_dials`). Negative control: the dial rule before the fix, run
  on B's database, would not dial it.

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
  /-- This node's key's secret: its first found or join writes it. -/
  nk : ByteArray
  addr : ByteArray
  path : String
  run : Runner

def side (dir name : String) (port : Nat) : IO Peer := do
  let seed := sha256 s!"seed {name}".toUTF8
  let nk := sha256 s!"node {name}".toUTF8
  let addr := s!"127.0.0.1:{port}".toUTF8
  let path := s!"{dir}/{name}.db"
  let db ← fresh path
  let x : Sync F (SqlM F) := { fam, cfg, hooks := hooks fam K addr }
  let run ← Runner.start x db 0 port.toUInt16
  return { name, seed, nk, addr, path, run }

def Peer.key (p : Peer) : ByteArray := cryptoSeal.pub p.nk

/-- Read a side's store through a connection of its own. -/
def look {α} (s : Peer) (q : SqlM F α) : IO α := do q.run (← Db.openAt s.path)

def ests (s : Peer) : IO (List Connection.Fact) := do
  return (← look s (rows established.all [] : SqlM F _)).map (·.2)

/-- A Community view, read on a side's store. -/
def viewOn {α} (s : Peer) (v : View Community.Fact α) : IO α := look s ((v.liftL : View F α).run : SqlM F α)

/-- The deliver step as it was before the bare-path fix: every shared op
of an opened hello's community, not only join requests. The negative
control: run on A's store, it takes what today's `react` leaves. -/
def oldDeliver : SqlM F (List Op) := do
  let mut out := []
  for (_, f) in ← (rows opened.all [] : SqlM F _) do
    let .opened _ c _ _ hs := f | continue
    for b in hs do
      let some o := Op.decode b | continue
      if decide (fam.scope o = .shared c) && (← (Store.getOp o.id : SqlM F _)).isNone then
        out := o :: out
  return out

/-- The dial rule before the rejoin fix: a pending join was skipped while
a session to the inviter was open and the inviter was let in for c.
What it would dial, as hints. The negative control. -/
def oldDial : SqlM F (List ByteArray) := do
  let joins : Answer F ← Lists.list (Community.joining.all.query [])
  let mut out := []
  for (_, f) in joins.lefts do
    let .joining c inviter hints _ _ d _ := f | continue
    let some hint := hints.head? | continue
    let some (me, _) ← ((Community.mine c).liftL : View F _).run | continue
    if me ≠ d then continue
    if ← (connectedTo inviter : SqlM F Bool) then
      if ← ((Community.allowPeer c inviter).liftL : View F Bool).run then continue
    out := hint :: out
  return out

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
  a.run.write (← viewOn a (found a.seed "Acme".toUTF8 "Ann".toUTF8 1 (sha256 "key".toUTF8)
    (sha256 "esk".toUTF8) a.nk)).ops
  let c := (root dA a.key).id
  -- the runner owns the writes: read once the founding has landed
  let _ ← waitFor 10000 (stored a c)
  let stopAll : IO UInt32 := do
    a.run.stop; b.run.stop
    let code ← t.finish "jointcp"
    (← IO.getStdout).flush
    IO.Process.exit code.toUInt8
  let some (wi, link) ← viewOn a (inviteTo c c a.seed (sha256 "bearer".toUTF8) [a.addr])
    | t.ok "tcp: A invites" false; stopAll
  t.ok "tcp: the link names A's node key" (link.inviter == a.key)
  a.run.write wi.ops
  let req := link.request dB b.key
  b.run.write (← viewOn b (join link b.seed "Bea".toUTF8 b.nk)).ops
  -- Before approval.
  let opened ← waitFor 10000 do return (← look a (count opened.all [] : SqlM F _)) ≥ 1
  t.ok "tcp: A opened B's request" opened.isSome
  t.ok "tcp: A stored B's join request" (← stored a req.id)
  IO.sleep 1000
  t.ok "tcp: A answered nothing before approval" ((← ests a).isEmpty)
  t.ok "tcp: B established nothing before approval" ((← ests b).isEmpty)
  t.ok "tcp: B is not admitted on A before approval" (!(← allowedOn a c b.key))
  -- A approves.
  let wr ← look a ((approveReq c req.id c a.seed).liftL.run : SqlM F Community.Write)
  a.run.write wr.ops
  let est ← waitFor 15000 do return (← ests a).length == 1 && (← ests b).length == 1
  t.ok "tcp: each holds one established session" est.isSome
  match ← ests a, ← ests b with
  | [.established ca _ pa ..], [.established cb _ pb ..] =>
    t.ok "tcp: the same connection id" (ca == cb)
    t.ok "tcp: each names the other by node key, never by device key"
      (pa == b.key && pb == a.key && pa != dB.pk && pb != dA.pk)
  | _, _ => t.ok "tcp: sessions have the expected shape" false
  -- Sync over the sealed session.
  let admitted ← waitFor 20000 do return (← allowedOn b c b.key) && (← allowedOn b c a.key)
  t.ok "tcp: B is admitted by its own ops, and lets A in" admitted.isSome
  let p := post c c dA "k".toUTF8 "hello B over TCP".toUTF8 5
  a.run.write [p]
  let streamed ← waitFor 10000 (stored b p.id)
  t.ok "tcp: a later post reaches B" streamed.isSome
  -- A second community between the same nodes: one session carries both.
  let seedA2 := sha256 "seed A, second".toUTF8
  a.run.write (← viewOn a (found seedA2 "Zed".toUTF8 "Ann".toUTF8 2 (sha256 "key Z".toUTF8)
    (sha256 "esk Z".toUTF8) (sha256 "unused".toUTF8))).ops
  let c' := (root (Device.ofSeed seedA2) a.key).id
  let _ ← waitFor 10000 (stored a c')
  let some (wiZ, linkZ) ← viewOn a (inviteTo c' c' seedA2 (sha256 "bearer Z".toUTF8) [a.addr])
    | t.ok "tcp: A invites to Zed" false; stopAll
  a.run.write wiZ.ops
  let seedB2 := sha256 "seed B, second".toUTF8
  b.run.write (← viewOn b (join linkZ seedB2 "Bea".toUTF8 (sha256 "unused".toUTF8))).ops
  let reqZ := linkZ.request (Device.ofSeed seedB2) b.key
  let _ ← waitFor 10000 (stored a reqZ.id)
  a.run.write (← look a ((approveReq c' reqZ.id c' seedA2).liftL.run : SqlM F Community.Write)).ops
  let inZed ← waitFor 20000 (allowedOn b c' b.key)
  t.ok "tcp: B joins a second community of A's, over its node key" inZed.isSome
  IO.println s!"jointcp: opened in {opened}, established in {est}, admitted in {admitted}, post in {streamed} (ms)"
  -- A removes B, on the live session.
  let adms ← look a ((Community.admission.byDevice.read [c, dB.pk]).liftL.run : SqlM F (Answer Community.Fact))
  match adms.rows.head? with
  | none => t.ok "tcp: A holds B's admission" false
  | some ((_, admB), _) =>
    let rm := remove c c c admB dA
    a.run.write [rm]
    let cut ← waitFor 5000 do return !(← allowedOn a c b.key)
    t.ok "tcp: A's trust rule refuses B's node once the removal is held" cut.isSome
    let p2 := post c c dA "k".toUTF8 "after the removal".toUTF8 6
    a.run.write [p2]
    let q := post c admB dB "k".toUTF8 "B, not knowing".toUTF8 7
    b.run.write [q]
    -- Well past the time the earlier post took to stream.
    IO.sleep 4000
    t.ok "tcp: B posted on its side" (← stored b q.id)
    t.ok "tcp: A's post after the removal does not reach B" (!(← stored b p2.id))
    t.ok "tcp: A does not take B's post" (!(← stored a q.id))
    IO.println s!"jointcp: removal held in {cut} ms; B holds the removal: {← stored b rm.id}; sessions on A: {(← ests a).length}"
    -- The bare path takes only a join: the removed B dials A with a
    -- fresh post in its hello, on a new request from B's node key.
    let q2 := post c admB dB "k".toUTF8 "pushed in a hello".toUTF8 8
    let e := sha256 "B's pushing ephemeral".toUTF8
    let some ro := Request.op K b.nk a.key e (hello c b.addr [q2])
      | t.ok "tcp: B composes a request" false; let _ ← stopAll
    b.run.write [ro, Eph.op e ro.id, Send.op a.addr ro]
    let openedPush ← waitFor 10000 do
      return (← look a (count Connection.opened.byRequest [ro.id] : SqlM F _)) ≥ 1
    t.ok "tcp: A opens the removed B's request" openedPush.isSome
    IO.sleep 1000
    t.ok "tcp: A does not store the post its hello carries" (!(← stored a q2.id))
    t.ok "tcp: and answers nothing: no connection for it"
      ((← look a (count connection.byRequest [ro.id] : SqlM F _)) == 0)
    let now ← look a (react fam K : SqlM F (List Op))
    t.ok "tcp: today's react, run on A's store, writes nothing of the hello's post"
      (!now.any (·.id == q2.id))
    let before ← look a oldDeliver
    t.ok "tcp: negative control: the deliver step before the fix takes it from that same store"
      (before.any (·.id == q2.id))
    -- A rejoin beside an open session. B comes to hold its removal (the
    -- notice will carry it; written here by hand): its entry for c is
    -- not held, and its session with A stays open for Zed.
    b.run.write [rm]
    let dropped ← waitFor 5000 do return (← viewOn b (Community.mine c)).isNone
    t.ok "tcp: B, holding its removal, holds c no more" dropped.isSome
    t.ok "tcp: and its session with A stays open for the community they still share"
      ((← ests b).length == 1 && (← allowedOn b c a.key))
    let some (wi3, link3) ← viewOn a (inviteTo c c a.seed (sha256 "bearer 3".toUTF8) [a.addr])
      | t.ok "tcp: A invites B again" false; let _ ← stopAll
    a.run.write wi3.ops
    let seedB3 := sha256 "seed B, rejoined".toUTF8
    let dB3 := Device.ofSeed seedB3
    b.run.write (← viewOn b (join link3 seedB3 "Bea".toUTF8 (sha256 "unused".toUTF8))).ops
    let req3 := link3.request dB3 b.key
    let _ ← waitFor 5000 do return (← viewOn b (Community.mine c)).isSome
    let now ← look b (dial K b.addr 0 : SqlM F (List Op))
    t.ok "tcp: today's dial, on B's store, sends the rejoin request beside the open session"
      (now.any fun o => match (Codec.decode o.body : Option Connection.Body) with
        | some (.send h) => h == a.addr
        | _ => false)
    let before ← look b oldDial
    t.ok "tcp: negative control: the dial rule before the fix would not send it" before.isEmpty
    let reached ← waitFor 10000 (stored a req3.id)
    t.ok "tcp: B's rejoin request reaches A bare, beside the open session" reached.isSome
    a.run.write (← look a ((approveReq c req3.id c a.seed).liftL.run : SqlM F Community.Write)).ops
    let back ← waitFor 20000 do
      return (← viewOn b (Community.mine c)).map (·.1) == some dB3.pk && (← allowedOn b c b.key)
    t.ok "tcp: approved, B is in c again as its new device, by its own ops" back.isSome
    t.ok "tcp: and A lets B's node in again" (← allowedOn a c b.key)
    IO.println s!"jointcp: rejoin request reached A in {reached} ms, B back in {back} ms"
  a.run.stop
  b.run.stop
  let code ← t.finish "jointcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
