/-
What a removed member's node sees, and whose keys a handshake runs on:
the Connection family's side of docs/REMOVAL.md, stated of the views
and validators the node runs. Statements (`_stmt`), proven in phase 2.

Read over the node's store (`DB F`, Community and Connection composed),
as `rooms_cut` is. Each connection step the node runs is a `Conn` step
on the connection `Node.refresh` leaves, `c.carry ((carriedV cid).eval s)`
on the model (phase 2: `carriedV` becomes `roomsV`, `carry` becomes
`setRooms`, and the `rooms` hook returns rooms with notices).

- E2 `rooms_removed_stmt`: when this node is a live member of c and the
  trust rule refuses the peer, the connection carries no synced room c,
  only notices of removals the peer's key is owed.
- E2 `removed_gets_only_notice_stmt`: so every op a connection step
  sends of c is a sync wire op or in the requirement closure of such a
  removal, and nothing of c is taken.
- E1 `notice_then_cut_stmt`: once every removal owed is given on the
  connection, it carries nothing; `sessions` drops it and `retired`
  names it, so the node closes it and purges its ops.
- E2 `answer_trusted_stmt`, `resend_trusted_stmt`: on the bare wire,
  `react` answers and `onArrival` re-sends an answer only for a request
  whose initiator the trust rule takes.
- E3 `opened_endpoint_stmt`, `established_endpoint_stmt`: the
  handshake's statics are the two nodes' keys: a side's static is the
  secret of the endpoint op its `opened` or `established` cites, the
  peer's is the request's other key. `meV_node_stmt`: the trust rule's
  "me" is this node's key.
-/
import Connection.Intents
import Connection.RoomLaws
import Engine.Sync.NoticeLaws

namespace Connection
open Engine Engine.Sync Codec

/-! ## Read over the node's store -/

/-- The (community, peer) pairs connection cid's established facts name. -/
def pairsAt (s : DB F) (cid : Id) : List (B × B) :=
  pairsOf (Engine.eval s (established.byConn.query [cid]))

/-- This node is a live member of c, as the trust rule reads it. -/
def LiveIn (s : DB F) (c : B) : Prop :=
  ∀ me, (meV c).eval s = some me → ((Community.allowPeer c me).liftL : View F Bool).eval s = true

/-- The trust rule refuses every peer connection cid names in c: once the
removal is held, a removed member's node. -/
def Refused (s : DB F) (cid c : B) : Prop :=
  ∀ peer, (c, peer) ∈ pairsAt s cid → ((Community.allowPeer c peer).liftL : View F Bool).eval s = false

/-- Removal x of community c is owed to connection cid's peer: a removal
of a user admitted under the peer's key, read from the lists. -/
def Owed (s : DB F) (cid c x : B) : Prop :=
  ∃ peer, (c, peer) ∈ pairsAt s cid ∧ x ∈ ((Community.removalsAt c peer).liftL : View F (List Id)).eval s

/-- What may go out of community c on cid: a sync wire op, an op of
another room, or an op in the requirement closure, in c, of a removal
owed to the peer. -/
def NoticeOnly (fam : Family F) (s : DB F) (cid c : B) (o : Op) : Prop :=
  isWire o.kind = true ∨ fam.room o ≠ some c ∨ ∃ x, Owed s cid c x ∧ ReachIn fam s.ops c x o.id

/-! ## E2: nothing but the notice -/

/-- **A removed member's connection carries only notices
(`rooms_removed`).** If this node is a live member of c and the trust
rule refuses every peer cid names in c, cid carries no synced room c,
and each notice of c it carries is of a removal owed to the peer. -/
def rooms_removed_stmt : Prop :=
  ∀ (s : DB F) (cid c : B), LiveIn s c → Refused s cid c →
    ∀ rm ∈ (carriedV cid).eval s, match rm with
      | .sync r => r ≠ c
      | .notice r x => r = c → Owed s cid c x

/-- **Nothing but the notice (`removed_gets_only_notice`).** Under the
same premises, on the connection as each step reads it afresh: opening
says hello only; and of community c, a frame received, ops just stored
(`filed`) and the clock (`tick`) send only sync wire ops and ops in the
requirement closure of a removal owed to the peer. A frame received
hands the writer nothing of c. -/
def removed_gets_only_notice_stmt : Prop :=
  ∀ (fam : Family F) (cfg : Config) (ix : Index) (s : DB F) (cid c : B) (conn : Conn)
    (bytes : B) (ids : List Id) (now floor : Nat) (dialer : Bool),
    LiveIn s c → Refused s cid c →
    let k := conn.carry ((carriedV cid).eval s)
    (∀ rs, ∀ o ∈ (Conn.open dialer rs floor now).send, isWire o.kind = true) ∧
    (∀ o ∈ ((Conn.recv fam cfg ix k bytes now : Model F Step).run s).1.send,
      NoticeOnly fam s cid c o) ∧
    (∀ o ∈ ((Conn.recv fam cfg ix k bytes now : Model F Step).run s).1.take, fam.room o ≠ some c) ∧
    (∀ o ∈ ((Conn.filed fam cfg k ids : Model F Step).run s).1.send, NoticeOnly fam s cid c o) ∧
    (∀ o ∈ ((Conn.tick fam cfg ix k now : Model F Step).run s).1.send, NoticeOnly fam s cid c o)

/-! ## E1: then the cut -/

/-- **Notice, then cut (`notice_then_cut`).** If this node is a live
member of c, the trust rule refuses cid's peer, cid is about c only, and
every removal owed to the peer is settled on cid (given: `conn.settled`),
then cid carries nothing, `sessions` does not list it, and `retired`
names it if it is an established session: the node closes it, and
`closing` purges its ops. -/
def notice_then_cut_stmt : Prop :=
  ∀ (s : DB F) (cid c : B), LiveIn s c → Refused s cid c →
    (∀ p ∈ pairsAt s cid, p.1 = c) →
    (∀ x, Owed s cid c x → x ∈ (givenOn cid).eval s) →
    (carriedV cid).eval s = [] ∧
    (∀ e ∈ ((sessions : Model F _).run s).1, e.1 ≠ cid) ∧
    ((∃ e ∈ ((allSessions : Model F _).run s).1, e.1 = cid) →
      cid ∈ ((retired : Model F _).run s).1)

/-! ## E2 on the bare wire -/

/-- **An answer only to the trusted (`answer_trusted`).** Every
connection op `react` writes answers a stored request r, opened here
for community c from key frm, addressed to `to`, where the trust rule
takes frm for c with `to` as this node: lean-net's "no connection
before approval", and after removal, no new session for a removed
member's node. -/
def answer_trusted_stmt : Prop :=
  ∀ (fam : Family F) (K : Keys) (fr : Fresh (Model F)) (s : DB F) (o : Op) (m2 : B),
    o ∈ ((@react _ _ _ _ fr fam K).run s).1 → (decode o.body : Option Body) = some (.connection m2) →
    ∃ r ro to frm' m1 c frm addr hs, o.reqs = [r] ∧ s.ops r = some ro ∧
      (decode ro.body : Option Body) = some (.request to frm' m1) ∧
      (.inr (.opened r c frm addr hs)) ∈ (Engine.eval s (opened.byRequest.query [r])).rows.map (·.2) ∧
      ((trusts c to frm).liftL : View F Bool).eval s = true

/-- **A re-sent answer only to the trusted (`resend_trusted`).** A
request arriving again, bare, gets its answer re-sent (a courier) only
if it was opened here for community c from key frm and the trust rule
still takes frm for c: a removed member's node replaying its request
gets nothing. -/
def resend_trusted_stmt : Prop :=
  ∀ (s : DB F) (addr : B) (o : Op) (at_ : Nat) (q : Op) (a : B),
    q ∈ ((onArrival none addr o at_ : Model F (List Op)).run s).1 →
    (decode q.body : Option Body) = some (.send a) →
    ∃ to frm' m1 c frm addr' hs, (decode o.body : Option Body) = some (.request to frm' m1) ∧
      (.inr (.opened o.id c frm addr' hs)) ∈
        (Engine.eval s (opened.byRequest.query [o.id])).rows.map (·.2) ∧
      ((trusts c to frm).liftL : View F Bool).eval s = true

/-! ## E3: the handshake runs on the nodes' keys -/

/-- **A responder opens with its node's key (`opened_endpoint`).** An
`opened` checks out only citing the request and an endpoint fact whose
key is the request's addressee; message 1 is read with that endpoint's
secret as the responder's static and the request's sender key as the
initiator's. -/
def opened_endpoint_stmt : Prop :=
  ∀ (K : Keys) (o : Op) (fs : List F) (r c frm addr : B) (hs : List B),
    Opened.check K o fs = some (.opened r c frm addr hs) →
    ∃ to m1 pk sk, fs = [.inr (.request to frm m1), .inl (.endpoint pk sk)] ∧ pk = to ∧
      (Noise.read1 K.suite prologue sk frm m1).isSome

/-- **A session is between two nodes' keys (`established_endpoint`).**
An `established` checks out only citing the connection, the request,
this side's ephemeral and an endpoint fact (pk, sk). The responder's
endpoint is the request's addressee and its peer the sender; the
initiator's is the sender and its peer the addressee; each side runs
its half of KK with sk as its static and the peer's key as the remote
static. Device keys never enter the handshake. -/
def established_endpoint_stmt : Prop :=
  ∀ (K : Keys) (o : Op) (fs : List F) (cid c peer h sk' rk : B) (dialer : Bool),
    Established.check K o fs = some (.established cid c peer h sk' rk dialer) →
    ∃ r m2 to frm m1 ofE pkE esk pk sk,
      fs = [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofE pkE esk),
        .inl (.endpoint pk sk)] ∧
      ((dialer = false ∧ pk = to ∧ peer = frm ∧ (Noise.read1 K.suite prologue sk frm m1).isSome) ∨
       (dialer = true ∧ pk = frm ∧ peer = to ∧ (Noise.sent1 K.suite prologue sk esk to m1).isSome))

/-- **"Me" is this node's key (`meV_node`).** The node is in c as its
key: `meV c` is this node's endpoint key, and only while `Community.mine`
names a device of c whose secret it holds. -/
def meV_node_stmt : Prop :=
  ∀ (s : DB F) (c me : B), (meV c).eval s = some me →
    (∃ sk, ((Community.nodeKey).liftL : View F _).eval s = some (me, sk)) ∧
    ∃ d a, ((Community.mine c).liftL : View F _).eval s = some (d, a)

end Connection
