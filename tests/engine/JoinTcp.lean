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
- Notice, then cut (docs/REMOVAL.md, E1 and E2): A removes B while
  their session is live and carries only Acme. A's next step gives B
  its removal and the removal's closure, and A closes the session. B is
  told: it holds its removal, which nothing but the notice carries. Its
  device is cut, it holds Acme no more, and it closes its side. Both
  ends purge the session; nothing reopens, and a post of A's after the
  removal does not reach B.
- The bare path takes only a join: the removed B dials A with a fresh
  post in its hello. A opens the request, stores neither the post nor
  anything for it, and answers nothing (`bare_takes_only_join`,
  `answer_trusted`). Negative control: the deliver step as it was
  before the fix, run on A's database, takes the post.
- B rejoins as a new device: A invites again, B joins with a new seed
  under its node key, and its request reaches A bare. A refuses B's node
  until it approves the new device, then lets it in; B is in Acme again
  by its own ops, and the old user stays removed.
- One session carries two communities: B joins A's Zed beside the open
  session. A removes B's new user from Acme: B is told, and the session
  stays open for Zed (`rooms_complete`): a post in Zed reaches B, one in
  Acme does not.
- A rejoin is dialed beside an open session: B joins Acme again as a
  third device; its request goes bare beside the session, A approves it,
  and B is let in again (`rejoin_dials`). Negative control: the dial
  rule before the fix, run on B's database, would not dial it.
- Before and after the removal, A's Community views, read from its
  store of both families, answer as a Community-only store of the
  Community ops A holds does (`sum_project_node`). Without the removal,
  that store would let B's node in (a negative control).
- Negative controls, each a pair of runners whose hooks are mutated: a
  rooms hook that gives no notices (B never learns its removal, and A
  keeps the session open), and sessions that do not read the rooms view
  (B is told, but the session stays open at both ends).

Each step is read from the runners' databases through a second
connection (SQLite's WAL lets it read beside the runner's writer).
-/
import tests.engine.Lib
import ops.connection.All

open Engine Engine.Sync Community Tests Connection

def K := sodium
def fam : Family F := node ed25519 K
def cfg : Config := { every := 30000, askTime := 20000 }

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

/-- The rooms hook with its notices dropped: synced rooms only. -/
def quietRooms (cid : Id) : SqlM F (List Room) := do
  return (Room.syncs (← (rooms cid : SqlM F _))).map .sync

/-- The sessions as they were before they read the rooms view: kept, one
per peer, whatever they carry; and the rest retired. -/
def oldSessions : SqlM F (List (Id × ByteArray × Bool)) := do
  let all ← (allSessions : SqlM F _)
  let k := kept all
  return all.filterMap fun (cid, _, dialer, a, _) => if k.contains cid then some (cid, a, dialer) else none

def oldRetired : SqlM F (List Id) := do
  let all ← (allSessions : SqlM F _)
  let k := kept all
  return all.filterMap fun (cid, _) => if k.contains cid then none else some cid

/-- A node's hooks, as the family gives them or mutated for a negative
control. -/
inductive Mutant where
  | none
  | quiet
  | old

def Mutant.apply : Mutant → Hooks F (SqlM F) → Hooks F (SqlM F)
  | .none, h => h
  | .quiet, h => { h with rooms := quietRooms }
  | .old, h => { h with established := oldSessions, retired := oldRetired }

def side (dir name : String) (port : Nat) (m : Mutant := .none) : IO Peer := do
  let seed := sha256 s!"seed {name}".toUTF8
  let nk := sha256 s!"node {name}".toUTF8
  let addr := s!"127.0.0.1:{port}".toUTF8
  let path := s!"{dir}/{name}.db"
  let db ← fresh path
  let x : Sync F (SqlM F) := { fam, cfg, hooks := m.apply (hooks fam K addr) }
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

/-- Whether device d is live in c, read on a side's store. -/
def liveOn (s : Peer) (c d : ByteArray) : IO Bool :=
  look s ((Community.deviceLive c d).liftL.run : SqlM F Bool)

def stored (s : Peer) (x : Id) : IO Bool := do return (← look s (Store.getOp x : SqlM F _)).isSome

/-- `sum_project_node`, run: A's trust rule for each of the node keys es,
its members and its recipients in c, read from its store of both
families, against the model of a Community-only node holding the
Community ops A holds. Returns those ops. While a session is open the
node holds Connection ops too (`mixed`); once the removal has cut it,
its ops are purged and only Community ops are left. -/
def projected (t : Checks) (tag : String) (s : Peer) (c : Id) (es : List ByteArray) (mixed : Bool) :
    IO (List Op) := do
  let (held, allowed, mem, rcp, queue) ← look s do
    let held ← dumpOps (F := F)
    let allowed ← es.mapM fun e => ((Community.allowPeer c e).liftL.run : SqlM F Bool)
    let mem ← ((Community.members c).liftL.run : SqlM F (List ByteArray))
    let rcp ← ((Community.recipients c).liftL.run : SqlM F (List ByteArray))
    let queue ← dumpQueue (F := F)
    return (held, allowed, mem, rcp, queue)
  let cops := held.filter fun o => !owns o.kind
  let m := modelRun (Community.family ed25519) cops
  t.ok s!"{tag}: the node is at rest, and so is its Community part" (queue.isEmpty && m.queue.isEmpty)
  if mixed then t.ok s!"{tag}: the node holds Connection ops too" (cops.length < held.length)
  t.ok s!"{tag}: the trust rule answers as the Community part's"
    (allowed == es.map fun e => (Community.allowPeer c e).eval m)
  t.ok s!"{tag}: members as the Community part's" (mem == (Community.members c).eval m)
  t.ok s!"{tag}: recipients as the Community part's" (rcp == (Community.recipients c).eval m)
  return cops

/-- Wait up to ms for p, checking every 50 ms; how long it took. -/
def waitFor (ms : Nat) (p : IO Bool) : IO (Option Nat) := do
  let t0 ← IO.monoMsNow
  while (← IO.monoMsNow) < t0 + ms do
    if ← p then return some ((← IO.monoMsNow) - t0)
    IO.sleep 50
  return none

/-- A founds Acme, B joins and is approved: B's admission, once B is
admitted by its own ops and the session is up. -/
def pairUp (a b : Peer) : IO (Option (Id × Id)) := do
  let dA := Device.ofSeed a.seed
  a.run.write (← viewOn a (found a.seed "Acme".toUTF8 "Ann".toUTF8 1 (sha256 "key".toUTF8)
    (sha256 "esk".toUTF8) a.nk)).ops
  let c := (root dA a.key).id
  let _ ← waitFor 10000 (stored a c)
  let some (wi, link) ← viewOn a (inviteTo c c dA (sha256 "bearer".toUTF8) [a.addr]) | return none
  a.run.write wi.ops
  let req := link.request (Device.ofSeed b.seed) b.key
  b.run.write (← viewOn b (join link b.seed "Bea".toUTF8 b.nk)).ops
  let _ ← waitFor 10000 (stored a req.id)
  a.run.write (← look a ((approveReq c req.id c dA).liftL.run : SqlM F Community.Write)).ops
  let ok ← waitFor 20000 do
    return (← allowedOn b c b.key) && (← ests a).length == 1 && (← ests b).length == 1
  if ok.isNone then return none
  let adms ← look a ((Community.admission.byDevice.read [c, (Device.ofSeed b.seed).pk]).liftL.run :
    SqlM F (Answer Community.Fact))
  return adms.rows.head?.map fun ((_, adm), _) => (c, adm)

/-- A negative control: a pair whose hooks are mutated, A removing B on
the live session; whether B was told within 4 s, and whether each end
still has the session. -/
def mutantRun (dir tag : String) (port : Nat) (m : Mutant) : IO (Bool × Bool × Bool) := do
  let a ← side dir s!"A-{tag}" port m
  let b ← side dir s!"B-{tag}" (port + 1) m
  let r ← pairUp a b
  let out ← match r with
    | none => pure (true, true, false)
    | some (c, admB) =>
      let rm := remove c c c admB (Device.ofSeed a.seed)
      a.run.write [rm]
      IO.sleep 4000
      pure (← stored b rm.id, !(← ests a).isEmpty, !(← ests b).isEmpty)
  a.run.stop; b.run.stop
  return out

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
  let some (wi, link) ← viewOn a (inviteTo c c dA (sha256 "bearer".toUTF8) [a.addr])
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
  let wr ← look a ((approveReq c req.id c dA).liftL.run : SqlM F Community.Write)
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
  let p := post c c dA "k".toUTF8 "hello B over TCP".toUTF8 1 5
  a.run.write [p]
  let streamed ← waitFor 10000 (stored b p.id)
  t.ok "tcp: a later post reaches B" streamed.isSome
  let _ ← projected t "tcp: before the removal" a c [a.key, b.key] true
  -- A removes B while their session is live and carries only Acme.
  let adms ← look a ((Community.admission.byDevice.read [c, dB.pk]).liftL.run : SqlM F (Answer Community.Fact))
  let some ((_, admB), _) := adms.rows.head? | t.ok "tcp: A holds B's admission" false; stopAll
  let rm := remove c c c admB dA
  a.run.write [rm]
  let cut ← waitFor 5000 do return !(← allowedOn a c b.key)
  t.ok "tcp: A's trust rule refuses B's node once the removal is held" cut.isSome
  let told ← waitFor 10000 (stored b rm.id)
  t.ok "tcp: B is told: it holds its removal, which only the notice carries" told.isSome
  let dropped ← waitFor 5000 do return (← viewOn b (Community.mine c)).isNone && !(← liveOn b c dB.pk)
  t.ok "tcp: B's device is cut on B, and B holds Acme no more" dropped.isSome
  let closed ← waitFor 10000 do return (← ests a).isEmpty && (← ests b).isEmpty
  t.ok "tcp: the session is cut at both ends, its ops purged" closed.isSome
  let cops ← projected t "tcp: after the removal" a c [a.key, b.key] false
  let without := modelRun (Community.family ed25519) (cops.filter (·.id != rm.id))
  t.ok "tcp: control: without the removal, the Community part lets B's node in"
    ((Community.allowPeer c b.key).eval without)
  let p2 := post c c dA "k".toUTF8 "after the removal".toUTF8 2 6
  a.run.write [p2]
  -- Well past the time the earlier post took to stream.
  IO.sleep 3000
  t.ok "tcp: A's post after the removal does not reach B" (!(← stored b p2.id))
  t.ok "tcp: and no session opens again" ((← ests a).isEmpty && (← ests b).isEmpty)
  IO.println s!"jointcp: removal held in {cut} ms, B told in {told} ms, session cut in {closed} ms"
  -- The bare path takes only a join: the removed B dials A with a fresh
  -- post in its hello, on a new request from B's node key.
  let q2 := post c admB dB "k".toUTF8 "pushed in a hello".toUTF8 4 8
  let e := sha256 "B's pushing ephemeral".toUTF8
  let some ro := Request.op K b.nk a.key e (hello c b.addr [q2])
    | t.ok "tcp: B composes a request" false; stopAll
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
  -- B rejoins as a new device, with no session open.
  let some (wi3, link3) ← viewOn a (inviteTo c c dA (sha256 "bearer 3".toUTF8) [a.addr])
    | t.ok "tcp: A invites B again" false; stopAll
  a.run.write wi3.ops
  let seedB3 := sha256 "seed B, rejoined".toUTF8
  let dB3 := Device.ofSeed seedB3
  b.run.write (← viewOn b (join link3 seedB3 "Bea".toUTF8 (sha256 "unused".toUTF8))).ops
  let req3 := link3.request dB3 b.key
  let reached ← waitFor 10000 (stored a req3.id)
  t.ok "tcp: B's rejoin request, a new device's under the same node key, reaches A bare" reached.isSome
  IO.sleep 500
  t.ok "tcp: A refuses B's node until it approves the new device"
    (!(← allowedOn a c b.key) && (← ests a).isEmpty)
  a.run.write (← look a ((approveReq c req3.id c dA).liftL.run : SqlM F Community.Write)).ops
  let back ← waitFor 20000 do
    return (← viewOn b (Community.mine c)).map (·.1) == some dB3.pk && (← allowedOn b c b.key)
  t.ok "tcp: approved, B is in Acme again as its new device, by its own ops" back.isSome
  t.ok "tcp: and A lets B's node in again" (← allowedOn a c b.key)
  t.ok "tcp: the old user stays removed, its device cut, on both"
    (!(← liveOn a c dB.pk) && !(← liveOn b c dB.pk) && (← stored a rm.id) && (← stored b rm.id))
  IO.println s!"jointcp: rejoin request reached A in {reached} ms, B back in {back} ms"
  -- A second community between the same nodes: one session carries both.
  let seedA2 := sha256 "seed A, second".toUTF8
  let dA2 := Device.ofSeed seedA2
  a.run.write (← viewOn a (found seedA2 "Zed".toUTF8 "Ann".toUTF8 2 (sha256 "key Z".toUTF8)
    (sha256 "esk Z".toUTF8) (sha256 "unused".toUTF8))).ops
  let c' := (root dA2 a.key).id
  let _ ← waitFor 10000 (stored a c')
  let some (wiZ, linkZ) ← viewOn a (inviteTo c' c' dA2 (sha256 "bearer Z".toUTF8) [a.addr])
    | t.ok "tcp: A invites to Zed" false; stopAll
  a.run.write wiZ.ops
  let seedB2 := sha256 "seed B, second".toUTF8
  b.run.write (← viewOn b (join linkZ seedB2 "Bea".toUTF8 (sha256 "unused".toUTF8))).ops
  let reqZ := linkZ.request (Device.ofSeed seedB2) b.key
  let _ ← waitFor 10000 (stored a reqZ.id)
  a.run.write (← look a ((approveReq c' reqZ.id c' dA2).liftL.run : SqlM F Community.Write)).ops
  let inZed ← waitFor 20000 do
    return (← allowedOn b c' b.key) && (← ests a).length == 1 && (← ests b).length == 1
  t.ok "tcp: B joins a second community of A's, beside the open session, over one session" inZed.isSome
  -- A removes B's new user from Acme: the session stays open for Zed.
  let adms3 ← look a ((Community.admission.byDevice.read [c, dB3.pk]).liftL.run : SqlM F (Answer Community.Fact))
  let some ((_, admB3), _) := adms3.rows.head? | t.ok "tcp: A holds B's new admission" false; stopAll
  let rm3 := remove c c c admB3 dA
  a.run.write [rm3]
  let told3 ← waitFor 10000 (stored b rm3.id)
  t.ok "tcp: removed again, beside Zed, B is told" told3.isSome
  let _ ← waitFor 5000 do return (← viewOn b (Community.mine c)).isNone
  IO.sleep 1000
  t.ok "tcp: and the session stays open for Zed"
    ((← ests a).length == 1 && (← ests b).length == 1 && (← allowedOn b c' a.key))
  let pZ := post c' c' dA2 "k".toUTF8 "still in Zed".toUTF8 1 9
  let p4 := post c c dA "k".toUTF8 "Acme, after the second removal".toUTF8 5 9
  a.run.write [p4, pZ]
  let zed ← waitFor 10000 (stored b pZ.id)
  t.ok "tcp: a post in Zed still reaches B" zed.isSome
  t.ok "tcp: one in Acme does not" (!(← stored b p4.id))
  -- A rejoin beside the open session: B joins Acme again, a third device.
  let some (wi4, link4) ← viewOn a (inviteTo c c dA (sha256 "bearer 4".toUTF8) [a.addr])
    | t.ok "tcp: A invites B a third time" false; stopAll
  a.run.write wi4.ops
  let seedB4 := sha256 "seed B, rejoined again".toUTF8
  let dB4 := Device.ofSeed seedB4
  b.run.write (← viewOn b (join link4 seedB4 "Bea".toUTF8 (sha256 "unused".toUTF8))).ops
  let req4 := link4.request dB4 b.key
  let _ ← waitFor 5000 do return (← viewOn b (Community.mine c)).isSome
  let now ← look b (dial K b.addr 0 : SqlM F (List Op))
  t.ok "tcp: today's dial, on B's store, sends the rejoin request beside the open session"
    (now.any fun o => match (Codec.decode o.body : Option Connection.Body) with
      | some (.send h) => h == a.addr
      | _ => false)
  let before ← look b oldDial
  t.ok "tcp: negative control: the dial rule before the fix would not send it" before.isEmpty
  let reached4 ← waitFor 10000 (stored a req4.id)
  t.ok "tcp: B's rejoin request reaches A bare, beside the open session" reached4.isSome
  a.run.write (← look a ((approveReq c req4.id c dA).liftL.run : SqlM F Community.Write)).ops
  let back4 ← waitFor 20000 do
    return (← viewOn b (Community.mine c)).map (·.1) == some dB4.pk && (← allowedOn b c b.key)
  t.ok "tcp: approved, B is in Acme again, beside Zed" back4.isSome
  a.run.stop
  b.run.stop
  -- Negative controls: the same removal with mutated hooks.
  let (toldQ, aOpenQ, _) ← mutantRun dir "quiet" (base + 2) .quiet
  t.ok "tcp: negative control: with a rooms hook giving no notices, B never learns its removal" (!toldQ)
  t.ok "tcp: and A keeps the session open, the notice owed" aOpenQ
  let (toldO, aOpenO, bOpenO) ← mutantRun dir "old" (base + 4) .old
  t.ok "tcp: negative control: with sessions not reading the rooms view, B is told but the session stays open at both ends"
    (toldO && aOpenO && bOpenO)
  let code ← t.finish "jointcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
