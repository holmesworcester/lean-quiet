/- Reachability supplement: real signed membership, Noise handshakes,
production hooks and authenticated transport rebinding in SQLite. The separate
plain-TCP fixture isolates admission order; this does not claim that its
one-row catalog is a complete production bootstrap execution. -/
import tests.engine.Lib
import app.Commands

namespace RetryReachability
open Engine Engine.Sync Community Tests Codec Connection

def author := Device.named "multiplex-authenticated-author"
def static (d : Device) := sha256 ("test node ".toUTF8 ++ d.pk)
def rootOp := root author (keyOf author) .empty
def fam := Connection.node ed25519 sodium

def run (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  let endpoint := Community.endpoint (static author)
  let mut ops := [rootOp, Community.secret (sha256 "multiplex-authenticated-author".toUTF8),
    Community.accept rootOp.id author.pk, endpoint]
  let mut ids : List Id := []
  let mut peers : List ByteArray := []
  for i in [0:3] do
    let remote := Device.named s!"multiplex-authenticated-peer-{i}"
    let bearer := Device.named s!"multiplex-authenticated-invitation-{i}"
    let invitation := Community.invite rootOp.id rootOp.id author bearer.pk false
    let member := Community.request rootOp.id invitation.id remote (keyOf remote) bearer.sk
    let approval := Community.approve rootOp.id member.id rootOp.id author
    let admission := Community.admit rootOp.id member.id approval.id
    let eI := sha256 s!"multiplex-authenticated-initiator-{i}".toUTF8
    let eR := sha256 s!"multiplex-authenticated-responder-{i}".toUTF8
    let some req := Request.op sodium (static remote) (keyOf author) eI
      (hello rootOp.id s!"127.0.0.1:{7500+i}".toUTF8 [member])
      | throw (IO.userError "genuine Noise request failed")
    let some (.request _ _ m1) := (decode req.body : Option Connection.Body)
      | throw (IO.userError "genuine Noise request decode failed")
    let some reply := Reply.op sodium req.id (static author) (keyOf remote) m1 eR
      | throw (IO.userError "genuine Noise response failed")
    let eph := Eph.op eR reply.id
    ops := ops ++ [invitation, member, approval, admission, req, reply, eph,
      Opened.op req.id endpoint.id, Established.op reply.id req.id eph.id endpoint.id,
      Recv.op req.id none s!"127.0.0.1:{7500+i}".toUTF8 (100+i)]
    ids := ids ++ [reply.id]
    peers := peers ++ [keyOf remote]
  (receive fam ops).run db
  let sessions ← (Connection.sessions : SqlM Connection.F _).run db
  t.ok "production hooks retain three distinct authenticated peers"
    (sessions.length == 3 && ids.all (fun cid => sessions.any (·.1 == cid)))
  let mut authorized := true
  let mut keys : List Id := []
  for cid in ids do
    let rooms ← (Connection.rooms cid : SqlM Connection.F _).run db
    authorized := authorized && rooms.any (fun r => match r with | .sync c => c == rootOp.id | _ => false)
    if let some peer ← (Connection.retryKey cid : SqlM Connection.F _).run db then keys := keys ++ [peer]
  t.ok "production retry identities are distinct validated peer keys"
    (keys == peers && keys.eraseDups.length == 3)
  t.ok "production shared-room authorization permits every authenticated session" authorized
  let x : Sync Connection.F (SqlM Connection.F) := {
    fam, hooks := Connection.hooks fam sodium "127.0.0.1:7499".toUTF8,
    cfg := { live := 1000000000, every := 1000000000 },
    catalog := some Catalog.sql, retryStore := some RetryStore.sql, deferredRetries := true,
    retryRoom := fun _ => some maxFrame }
  let (initial, _) ← ((Node.boot fam ops 0).finish x {} 100).run db
  let mut node := initial
  let shared := "127.0.0.1:7999".toUTF8
  let mut opened := true
  for cid in ids do
    let some (_, receiveKey) ← (Connection.sessionKeys cid : SqlM Connection.F _).run db
      | throw (IO.userError "validated Noise transport keys absent")
    let nonce := (sha256 ("shared-route".toUTF8 ++ cid)).extract 0 24
    let inner := Codec.encode ([] : List ByteArray)
    let sealed := Frame.seal sodium cid receiveKey nonce inner
    let actual ← (Connection.openFrame sodium sealed : SqlM Connection.F _).run db
    opened := opened && actual.any (fun pair => pair.1 == cid && pair.2 == inner)
    let (next, _) ← (node.onFrame x shared (ByteArray.mk #[sealedTag] ++ sealed) 101).run db
    node := next
  t.ok "actual Noise receive keys authenticate all three relay frames" opened
  t.ok "actual Node learns one shared socket address for three authorized sessions"
    (node.conns.length == 3 && ids.all (fun cid => node.addr? cid == some shared))
  let (followed, _) ← (node.finish x {} 102).run db
  t.ok "production follow preserves authenticated transport rebinding"
    (followed.conns.length == 3 && ids.all (fun cid => followed.addr? cid == some shared))

end RetryReachability
