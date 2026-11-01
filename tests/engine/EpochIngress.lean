/- Diagnostic of delivered native ingress versus session timeout. Both peers
use actual Connection hooks, signed membership, Noise/AEAD, SQLite, TCP reader,
writer and Loop.turn/RunState.loopBackend. Pausing between turns is explicit;
there is no claimed infinite execution theorem here. -/
import tests.engine.Lib
import app.connection.Proofs
import app.Commands

namespace JoinFair
open Engine Engine.Sync Community Connection Tests
def fam : Family F := node ed25519 sodium
def key := sha256 "join-fair/content-key".toUTF8
def seed (name : String) := sha256 s!"join-fair/device/{name}".toUTF8
def nk (name : String) := sha256 s!"join-fair/node/{name}".toUTF8
def device (name : String) := Device.ofSeed (seed name)
def nodeKey (name : String) := cryptoSeal.pub (nk name)
def postAt (c adm : Id) (name : String) (i : Nat) (text : ByteArray) : Op :=
  let nonce := (sha256 s!"join-fair/nonce/{name}/{i}".toUTF8).extract 0 24
  sealedPost c adm (device name) key nonce text i (1000 + i)
end JoinFair

namespace EpochIngress
def silenceMs : Nat := 5000

open Engine Engine.Sync Community Connection Tests Std.Async Std.Net

structure Peer where
  x : Sync F (SqlM F)
  cfg : RunConfig
  ch : Std.CloseableChannel.Sync Event
  writes : Std.CloseableChannel.Sync (List Op)
  state : Loop.State RunState
  notify : List Id → IO Unit := fun _ => pure ()

def tick (p : Peer) : IO Peer := do
  let r ← Loop.turn (RunState.loopBackend p.x p.ch p.notify p.cfg p.writes p.state.value.ingress)
    p.cfg.tickMs p.state
  if r.stopped then throw (IO.userError "unexpected diagnostic shutdown")
  return { p with state := r.state }

def stop (p : Peer) : IO Unit := do
  discard <| p.state.value.shutdown p.x p.ch p.cfg p.writes (← IO.monoMsNow)

def pending (p : Peer) : IO (List Event) :=
  p.state.value.ingress.registry.atomically do
    return (← getThe (Ingress.Registry Event p.state.value.ingress.peers)).state.slots.toArray.toList.filterMap id

def queuedTarget (p : Peer) (target : Op) : IO (Option ByteArray) := do
  for event in ← pending p do
    let .frame _ bytes := event | continue
    if bytes[0]? != some sealedTag then continue
    let some (_, payload) ← (p.x.hooks.openFrame (bytes.extract 1 bytes.size)).run p.state.value.db | continue
    let ops := ((Codec.decode payload : Option (List ByteArray)).getD []).filterMap Op.decode
    if ops.any (·.id == target.id) then return some bytes
  return none

def view {α} (p : Peer) (v : View Community.Fact α) : IO α :=
  (v.liftL.run : SqlM F α).run p.state.value.db

def has (p : Peer) (op : Op) : IO Bool := do
  return (← (Store.getOp op.id : SqlM F _).run p.state.value.db) == some op

def shared (a b : Peer) : Bool :=
  a.state.value.node.conns.any fun (cid, _) => b.state.value.node.conns.any (·.1 == cid)

def make (dir : String) (name : String) (address : ByteArray) (live idle : Nat) : IO Peer := do
  IO.FS.createDirAll dir
  let db ← Db.openAt (dir ++ "/" ++ name ++ ".db")
  let x : Sync F (SqlM F) := {
    fam := JoinFair.fam, cfg := { live, every := 30000, askTime := 20000 },
    hooks := hooks JoinFair.fam sodium address,
    catalog := some Catalog.sql, retryStore := some RetryStore.sql, deferredRetries := true }
  let cfg : RunConfig := { tickMs := 20, idle, stallMs := 5000, stopMs := 250, maxSocks := 4 }
  let ch ← eventChannel cfg
  let writes ← Std.CloseableChannel.Sync.new (some cfg.queue)
  let slots ← Std.Mutex.new []
  let (ingress, _) ← Ingress.Hub.new cfg.maxSocks
  return { x, cfg, ch, writes, state := { value := { db, node := Node.boot x.fam [] 0, slots, ingress } } }

def attach (p : Peer) (client : TCP.Socket.Client) (address : ByteArray) : IO Peer := do
  unless ← p.state.value.slots.take p.cfg address do throw (IO.userError "native slot refused")
  let (state, sid) ← p.state.value.addSock p.ch p.cfg client address (← IO.monoMsNow)
  unless sid.isSome do throw (IO.userError "native ingress source refused")
  return { p with state := { p.state with value := state } }

def submit (p : Peer) (ops : List Op) : IO Unit := do
  unless ← p.writes.trySend ops do throw (IO.userError "diagnostic write queue full")

def setup (dir : String) (live : Nat := silenceMs) (idle : Nat := 600000) : IO (Peer × Peer × Id × Id) := do
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  srv.listen 1
  let address := (addrText (← srv.getSockName)).toUTF8
  let client ← TCP.Socket.Client.mk
  let .ok _ ← awaitUv (client.native.connect (← srv.getSockName)) | throw (IO.userError "diagnostic connect")
  let mut accepted := none
  for _ in [0:1000] do
    if accepted.isNone then accepted ← srv.tryAccept
    if accepted.isSome then break
    IO.sleep 1
  let some server := accepted | throw (IO.userError "diagnostic accept")
  closeListener srv.native
  let remote := (addrText (← server.getPeerName)).toUTF8
  let mut a ← attach (← make dir "A" address live idle) server remote
  let mut b ← attach (← make dir "B" remote live idle) client address
  let c := (root (JoinFair.device "A") (JoinFair.nodeKey "A")).id
  submit a (← view a (found (JoinFair.seed "A") "Epoch probe".toUTF8 "Alice".toUTF8 1 JoinFair.key
    (sha256 "epoch-wrap".toUTF8) (JoinFair.nk "A"))).ops
  a ← tick a
  let some (inv, link) ← view a (inviteTo c c (JoinFair.device "A")
    (sha256 "epoch-bearer".toUTF8) [address]) | throw (IO.userError "diagnostic invitation")
  submit a inv.ops
  a ← tick a
  let req := link.request (JoinFair.device "B") (JoinFair.nodeKey "B")
  submit b (← view b (join link (JoinFair.seed "B") "Bob".toUTF8 (JoinFair.nk "B"))).ops
  for _ in [0:4000] do
    a ← tick a
    b ← tick b
    if ← has a req then break
    IO.sleep 1
  unless ← has a req do throw (IO.userError "actual bare request did not reach founder")
  submit a (← view a (approveReq c req.id c (JoinFair.device "A"))).ops
  for _ in [0:4000] do
    a ← tick a
    b ← tick b
    if shared a b && (← view b (allowPeer c (JoinFair.nodeKey "B"))) then break
    IO.sleep 1
  unless shared a b do throw (IO.userError "actual Noise handshake did not establish shared session")
  let adms ← view b (admission.byDevice.read [c, (JoinFair.device "B").pk])
  let some ((_, adm), _) := adms.rows.head? | throw (IO.userError "missing signed Bob admission")
  return (a, b, c, adm)

/-- Process only a mailbox already inspected, so the fixture never consumes
an asynchronously arriving target between inspection and polling. -/
def capture (a0 b0 : Peer) (c adm : Id) (name : String) (minSlot : Nat := 1) : IO (Peer × Peer × Op × ByteArray) := do
  let mut a := a0
  let mut b := b0
  for attempt in [0:12] do
    let target := JoinFair.postAt c adm name (7000 + attempt) s!"native queued target {attempt}".toUTF8
    submit a [target]
    for _ in [0:6000] do
      a ← tick a
      IO.sleep 1
      if let some bytes ← queuedTarget b target then
        if minSlot ≤ b.state.slot.val then return (a, b, target, bytes)
        -- This target happens to arrive on the network-preferred phase;
        -- accept it normally and try a later real post on a local phase.
        b ← tick b
        break
      unless (← pending b).isEmpty do b ← tick b
    if ← has b target then pure ()
    else throw (IO.userError "target did not enter native mailbox")
  throw (IO.userError "no local-preferred target capture")

def runCase (t : Checks) (dir : String) (localFirst : Bool) (socketIdle : Bool := false) : IO Unit := do
  let (a, b, c, adm) ← setup dir (if socketIdle then 1000000 else silenceMs) (if socketIdle then silenceMs else 600000)
  let (a, b, target, _bytes) ← capture a b c c "A"
  let some (cid, _) := b.state.value.node.conns.head? | throw (IO.userError "missing established session")
  t.ok "real signed membership and one shared Noise session" (shared a b &&
    (← view a (allowPeer c (JoinFair.nodeKey "B"))) && (← view b (allowPeer c (JoinFair.nodeKey "A"))))
  t.ok "target is held only by source before its native mailbox is serviced" ((← has a target) && !(← has b target))
  t.ok "native reader already admitted target and actual receive key decrypts it"
    ((← queuedTarget b target).isSome && (← (sessionKeys cid : SqlM F _).run b.state.value.db).isSome)
  t.ok "captured phase preserves actual local-first selector history" (b.state.slot.val != 0)
  let age := (← IO.monoMsNow) - ((b.state.value.node.conn? cid).map (·.heard)).getD 0
  let phase := b.state.slot.val
  IO.sleep (silenceMs + 100).toUInt32
  if localFirst then
    submit b [JoinFair.postAt c adm "B" 8000 "local work after finite process pause".toUTF8]
  let beforeEvents := (← pending b).length
  let mut b ← tick b
  if localFirst then
    t.ok "UI-first write completes while one-shot grace preserves admitted target"
      (!(← has b target) && !b.state.value.node.conns.isEmpty && !b.state.value.socks.isEmpty &&
        (← has b (JoinFair.postAt c adm "B" 8000 "local work after finite process pause".toUTF8)))
    t.ok "expiry grants the exact bounded source opportunity without consuming its frame"
      (beforeEvents > 0 && (← queuedTarget b target).isSome &&
        (if socketIdle then b.state.value.socketGrace.any (fun (_, g) => g.left == ExpiryGrace.budget b.cfg.maxSocks)
        else b.state.value.sessionGrace.any (fun (id, g) => id == cid && g.left == ExpiryGrace.budget b.cfg.maxSocks)))
    let mut turns := 0
    for i in [0:ExpiryGrace.budget b.cfg.maxSocks] do
      if ← has b target then break
      submit b [JoinFair.postAt c adm "B" (8100+i) s!"continuing local {i}".toUTF8]
      IO.sleep 22
      b ← tick b
      turns := turns + 1
    t.ok "admitted authenticated target is applied within its selector budget despite continuing writes"
      ((← has b target) && turns ≤ ExpiryGrace.budget b.cfg.maxSocks &&
        (← (sessionKeys cid : SqlM F _).run b.state.value.db).isSome)
  else
    t.ok "processing the same ready peer source before timeout accepts the target"
      ((← has b target) && !b.state.value.node.conns.isEmpty && !b.state.value.socks.isEmpty)
    let sa ← (Store.getStatus target.id : SqlM F _).run a.state.value.db
    let sb ← (Store.getStatus target.id : SqlM F _).run b.state.value.db
    t.ok "accepted target has the same valid derived fact as source"
      (Codec.encode sa == Codec.encode sb && sb.any (fun v => match v with | .valid _ => true | _ => false))
  IO.println s!"epoch-ingress case localFirst={localFirst} socketIdle={socketIdle} phase={phase} capturedAgeMs={age} beforeReady={beforeEvents} targetHeld={← has b target} sessions={b.state.value.node.conns.length} sockets={b.state.value.socks.length}"
  stop b
  stop a

/-- Malformed-to-trust but well-formed Noise requests create real arrival
notifications while never authenticating this already-established peer.
The notification barrier lets the actual native reader refill its one slot
before the subsequent timer; it does not manufacture an ingress event. -/
def junkCase (t : Checks) (dir : String) : IO Unit := do
  let (a, b0, c, adm) ← setup dir
  let some sock := a.state.value.socks.head? | throw (IO.userError "missing native sender")
  let mut b := b0
  let untrusted := sha256 "untrusted Noise initiator secret".toUTF8
  let junk := (List.range 100).filterMap fun i =>
    (Request.op sodium untrusted (JoinFair.nodeKey "B") (sha256 s!"untrusted epoch {i}".toUTF8)
      (hello c "127.0.0.1:1".toUTF8 [])).map fun r => tagged bareTag r.bytes
  t.ok "untrusted producer creates actual distinct Noise requests" (junk.length == 100)
  unless ← sock.push a.cfg (junk.map (.urgent, ·)) do throw (IO.userError "junk native send refused")
  -- Drain only earlier authenticated frames. The first malicious request
  -- stays owed and is processed by the actual selector after the pause.
  let mut found := false
  for _ in [0:2000] do
    let ready ← pending b
    if ready.any (fun e => match e with | .frame _ p => junk.contains p | _ => false) then
      if b.state.slot.val != 0 then found := true; break
    unless ready.isEmpty do b ← tick b
    IO.sleep 1
  unless found do throw (IO.userError "native junk never became a local-phase owed input")
  let some (cid, conn) := b.state.value.node.conns.head? | throw (IO.userError "junk setup session vanished")
  let hub := b.state.value.ingress
  let notify : List Id → IO Unit := fun _ => do
    for _ in [0:100] do
      let state ← hub.registry.atomically do
        let r ← getThe (Ingress.Registry Event hub.peers)
        return !(r.state.slots.toArray.toList.filterMap id).isEmpty
      if state then return
      -- Control slot zero is always live; the real peer source is gone
      -- when no live peer entries remain, after authenticated expiry.
      let peers ← hub.registry.atomically do
        return (← getThe (Ingress.Registry Event hub.peers)).live.toArray.toList.drop 1 |>.any id
      unless peers do return
      IO.sleep 1
    throw (IO.userError "native junk producer failed to refill its actual mailbox")
  b := { b with notify }
  IO.sleep (silenceMs + 100).toUInt32
  submit b [JoinFair.postAt c adm "B" 9000 "local work beside untrusted input".toUTF8]
  b ← tick b
  t.ok "pending junk grants only the same finite initial opportunity"
    (b.state.value.sessionGrace.any fun (id, g) => id == cid && g.heard == conn.heard &&
      g.left == ExpiryGrace.budget b.cfg.maxSocks)
  let mut turns := 0
  for i in [0:ExpiryGrace.budget b.cfg.maxSocks + 1] do
    if b.state.value.node.conns.isEmpty then break
    submit b [JoinFair.postAt c adm "B" (9100+i) s!"local beside junk {i}".toUTF8]
    IO.sleep 22
    b ← tick b
    turns := turns + 1
  t.ok "sustained untrusted requests cannot reset grace or retain the honest session key"
    (b.state.value.node.conns.isEmpty && turns ≤ ExpiryGrace.budget b.cfg.maxSocks &&
      (← (sessionKeys cid : SqlM F _).run b.state.value.db).isNone)
  t.ok "expired untrusted ingress is retired and cannot retain its native source"
    (b.state.value.socks.isEmpty && (← pending b).isEmpty)
  IO.println s!"epoch-ingress junk selections={turns} budget={ExpiryGrace.budget b.cfg.maxSocks} sessionGone={b.state.value.node.conns.isEmpty}"
  stop b
  stop a

def removalCase (t : Checks) (dir : String) : IO Unit := do
  let (a0, b0, c, adm) ← setup dir
  let (b, a, target, _) ← capture b0 a0 c adm "B" 2
  let some (cid, _) := a.state.value.node.conns.head? | throw (IO.userError "missing removal session")
  IO.sleep (silenceMs + 100).toUInt32
  submit a [JoinFair.postAt c c "A" 10000 "local work before explicit removal".toUTF8]
  let mut a ← tick a
  t.ok "removal fixture has an active grace and an admitted honest target"
    ((← queuedTarget a target).isSome && a.state.value.sessionGrace.any (fun (id, g) => id == cid && g.left > 0))
  let adms ← view a (admission.byDevice.read [c, (JoinFair.device "B").pk])
  let some (_, .admission _ user _ _) := adms.rows.head? | throw (IO.userError "missing removal target")
  let removal ← view a (removeMember c user (JoinFair.device "A"))
  t.ok "real founder removal intent produces one authenticated operation" (removal.ops.length == 1)
  submit a removal.ops
  a ← tick a
  t.ok "authenticated retirement bypasses active silence grace and erases keys immediately"
    (a.state.value.node.conns.isEmpty && a.state.value.socks.isEmpty &&
      (← (sessionKeys cid : SqlM F _).run a.state.value.db).isNone &&
      !(← view a (allowPeer c (JoinFair.nodeKey "B"))))
  t.ok "retirement cancels the old admitted target without applying unauthorized traffic"
    (!(← has a target) && (← pending a).isEmpty)
  let mut b := b
  -- Admit native output before resuming this receiver. An in-flight notice
  -- with an empty mailbox is outside the one-shot admitted-input guarantee.
  for _ in [0:500] do
    unless (← pending b).isEmpty do break
    IO.sleep 1
  for _ in [0:500] do
    b ← tick b
    if !(← view b (allowPeer c (JoinFair.nodeKey "B"))) then break
    IO.sleep 1
  t.ok "actual retirement writer drains the signed removal notice to its peer"
    (!(← view b (allowPeer c (JoinFair.nodeKey "B"))))
  stop b
  stop a

end EpochIngress

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/epoch-ingress"
  let t ← Tests.Checks.new
  EpochIngress.runCase t (dir ++ "/local") true
  EpochIngress.runCase t (dir ++ "/peer") false
  EpochIngress.runCase t (dir ++ "/socket-idle") true true
  EpochIngress.junkCase t (dir ++ "/junk")
  EpochIngress.removalCase t (dir ++ "/removal")
  let result ← t.finish "epoch-ingress"
  (← IO.getStdout).flush
  IO.Process.exit result.toUInt8
