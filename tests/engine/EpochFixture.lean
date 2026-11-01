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
def key := Bytes.digest "join-fair/content-key".toUTF8
def seed (name : String) := sha256 s!"join-fair/device/{name}".toUTF8
def nk (name : String) := Bytes.digest s!"join-fair/node/{name}".toUTF8
def device (name : String) := Device.ofSeed (seed name)
def nodeKey (name : String) := cryptoSeal.pub (nk name)
def postAt (c adm : Id) (name : String) (i : Nat) (text : ByteArray) : Op :=
  let nonce := (Bytes.fit 24 (sha256 s!"join-fair/nonce/{name}/{i}".toUTF8))
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
  let c := (root (JoinFair.device "A") (JoinFair.nodeKey "A") (kidOf cryptoSeal JoinFair.key)).id
  submit a (← view a (found (JoinFair.seed "A") "Epoch probe".toUTF8 "Alice".toUTF8 1 JoinFair.key
    (Bytes.digest "epoch-wrap".toUTF8) (JoinFair.nk "A"))).ops
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
    unless ← has b target do throw (IO.userError "target did not enter native mailbox")
    -- One extra receiver turn before the next attempt. Steady traffic moves
    -- the phase by the same count every attempt, so without this shift the
    -- attempts could cycle through the same network-preferred phases.
    b ← tick b
  throw (IO.userError "no local-preferred target capture")

end EpochIngress
