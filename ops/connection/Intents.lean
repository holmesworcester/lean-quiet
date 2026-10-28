/-
The connection family's reactions and commands: views over lists that
return the ops to write. The node runs `react` after every write and
`dial` on every tick, and writes what they return. Nothing here sends
anything, or decides anything outside ops.

A node handshakes with its own key (Community's `endpoint`), and a
session is one per peer key: it carries a room for every community this
node holds where the trust rule takes the peer (`roomsV`), whatever
community its hello named.

`react`, for this node:
- **open**: every request to its key with no `opened` gets one.
- **deliver**: of an opened request's hello, the join requests of its
  community, if not yet stored, go to the writer. This is how a joiner's
  request reaches the members, before anyone approves it. Nothing else a
  hello carries is taken, trusted or not (`bare_takes_only_join`): a
  trusted peer's ops travel on the session.
- **answer**: an opened request with no connection, whose initiator the
  trust rule admits for the hello's community, gets an ephemeral, the
  connection, this side's `established`, and a courier back to the
  address the request arrived from. A request the rule does not admit
  gets nothing, so the request opens nothing (`answer_trusted`).
- **establish**: a connection answering one of this node's requests,
  with no `established`, gets this side's.

`dial`, on a tick: for each pending join of this node's own entry, its
request to the inviter's key (the one whose hello delivers the join's
request) is resent on a courier to the link's first hint, or composed
if there is none yet: while the join's device is not admitted, until a
connection answers it, beside an open session or not; once admitted,
while no session to the inviter is open (`rejoin_dials`,
`reconnect_dials`). A tick is the retry: lean-net's "the joiner
re-sends the same hello every tick".

`closing cid`: what a closed session purges: the connection and its
request. Purge takes every dependent with them.

They run in any monad that reads lists and ops and gives fresh
secrets: the node's SQLite monad, with the OS's random bytes, or the
engine's model, so the same code runs in proofs by induction over a
world of nodes.
-/
import ops.connection.Family
import ops.connection.Frame
import engine.wire.Node
import ops.sync.Notice

namespace Connection
open Engine Engine.Sync Codec

/-- The trust rule (lean-net's), on node keys: `peer`'s node is let in
for c by this node's ops (a live device of c is admitted under its key);
or, before this node (`me`, its key) is let in for c, `peer` is the
inviter key a pending join names and this node's ops know nothing of it
in c yet. -/
def trusts (c me peer : B) : View Community.Fact Bool := do
  if ← Community.allowPeer c peer then return true
  let joins ← Community.joining.all.read []
  let linked := joins.rows.any fun (_, f) => match f with
    | .joining c' k _ _ _ _ _ => decide (c' = c ∧ k = peer)
    | _ => false
  if !linked then return false
  let admitted ← Community.allowPeer c me
  let known ← Community.admission.byKey.read [c, peer] (limit := some 0)
  return !admitted && known.total = 0

instance [Codec F] [SortKey F] : Fresh (SqlM F) := ⟨Noise.randomBytes 32⟩

/-- This node's key, while it is in community c: `Community.mine` names a
device of c whose secret it holds, live or waiting on a join. -/
def meV (c : B) : View F (Option B) := do
  let some _ ← ((Community.mine c).liftL : View F _) | return none
  let k ← ((Community.nodeKey).liftL : View F _)
  return k.map (·.1)

/-- The peer keys connection cid's established facts name. -/
def peersOf (a : Answer F) : List B :=
  a.rights.filterMap fun (_, f) => match f with
    | .established _ _ peer .. => some peer
    | _ => none

/-- The communities this node has accepted, each once: the ones a
session may carry. -/
def heldV : View F (List B) := do
  let a ← View.read (F := F) (Community.accepted.all.query [])
  return (a.lefts.filterMap fun (_, f) => match f with
    | .accepted c _ => some c
    | _ => none).eraseDups

/-- The notices given on connection cid (`conn.given`). -/
def givenOn (cid : Id) : View F (List Id) := do
  let a ← View.read (F := F) (given.byConn.query [cid])
  return a.rights.filterMap fun (_, f) => match f with
    | .given _ x => some x
    | _ => none

/-- What a connection carries of community c for peer key `peer`: the
room, synced, where this node is a device of c and the trust rule takes
the peer; else a notice of each removal that cuts a device under the
peer's key (`Community.removalsAt`) and is not yet given on it
(`given`); else nothing. -/
def roomFor (given : List Id) (c peer : B) : View F (List Room) := do
  match ← meV c with
  | some me =>
    let ok ← ((trusts c me peer).liftL : View F Bool)
    if ok then return [Room.sync c]
    let xs ← ((Community.removalsAt c peer).liftL : View F (List Id))
    return (xs.filter fun x => !has given x).map (Room.notice c)
  | none => return []

/-- What a connection carries for these (community, peer) pairs. -/
def roomsOf (given : List Id) : List (B × B) → View F (List Room)
  | [] => pure []
  | (c, peer) :: rest => do
    let here ← roomFor given c peer
    let tail ← roomsOf given rest
    return here ++ tail

/-- What connection cid carries now, as a view read afresh on every
step (docs/REMOVAL.md): for each community this node holds and each
peer key cid's established facts name, the room synced, or the notices
owed to a removed member's node, or nothing. A session is one per peer
key, and carries every community both nodes share, whatever its hello
named. A session that carries nothing is retired (`sessions`). -/
def roomsV (cid : Id) : View F (List Room) := do
  let a ← View.read (F := F) (established.byConn.query [cid])
  let given ← givenOn cid
  let cs ← heldV
  roomsOf given ((peersOf a).flatMap fun peer => cs.map (·, peer))

section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- This family's rows of a relation: op id and fact. -/
def rows (r : Rel Fact) (args : List B) : m (List (Id × Fact)) := do
  let a : Answer F ← Lists.list (m := m) (r.query args)
  return a.rights.map fun ((_, x), f) => (x, f)

def count (r : Rel Fact) (args : List B) : m Nat := do
  let a : Answer F ← Lists.list (m := m) (r.query args (limit := some 0))
  return a.total

/-- Byte order on ids. -/
def lt (a b : B) : Bool := a.toList < b.toList

/-- This node's keys: each endpoint op's public key, secret and id (one,
the first `found` or `join` writes it). -/
def endpoints : m (List (B × B × Id)) := do
  let a : Answer F ← Lists.list (m := m) (Community.endpoint.all.query [])
  return a.lefts.filterMap fun ((_, x), f) => match f with
    | .endpoint pk sk => some (pk, sk, x)
    | _ => none

/-- The bare address op x arrived from, if it arrived bare. -/
def arrivedFrom (x : Id) : m (Option B) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a _ => some a
    | _ => none

/-- open: an `opened`, citing this node's endpoint op, for each of these
requests to its key not opened yet. -/
def openEach (epOp : Id) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (r, _) :: t => do
    let n ← count opened.byRequest [r]
    let rest ← openEach epOp t
    return if n = 0 then Opened.op r epOp :: rest else rest

def openAll : List (B × B × Id) → m (List Op)
  | [] => pure []
  | (pk, _, epOp) :: t => do
    let a ← openEach epOp (← rows request.byTo [pk])
    let b ← openAll t
    return a ++ b

/-- Whether op o is a join request of community c: the one thing a
hello delivers. -/
def joinOf (c : B) (o : Op) : Bool :=
  decide (o.reqs.head? = some c) &&
    decide (o.kind = Community.Body.tag (.request .empty .empty .empty .empty)) &&
    match (decode o.body : Option Community.Body) with
    | some (.request ..) => true
    | _ => false

/-- deliver: of a hello of community c, the join requests of c not stored
yet. Nothing else of a hello is taken. -/
def joinsOf (fam : Family F) (c : B) : List B → m (List Op)
  | [] => pure []
  | b :: t => do
    let rest ← joinsOf fam c t
    match Op.decode b with
    | none => return rest
    | some o =>
      if joinOf c o && decide (fam.scope o = .shared c) then
        let held ← Store.getOp (m := m) o.id
        return if held.isNone then o :: rest else rest
      else return rest

def deliverAll (fam : Family F) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (_, .opened _ c _ _ hs) :: t => do
    let a ← joinsOf fam c hs
    let b ← deliverAll fam t
    return a ++ b
  | _ :: t => deliverAll fam t

/-- answer: an opened request r of community c from key frm, with no
connection yet, to one of this node's keys, whose initiator the trust
rule takes: an ephemeral, the connection, this side's `established`, and
a courier back to the address the request arrived from. -/
def answerOne (K : Keys) (eps : List (B × B × Id)) (r c frm : B) : m (List Op) := do
  if (← count connection.byRequest [r]) ≠ 0 then return []
  let some ro ← Store.getOp (m := m) r | return []
  let some (.request to _ m1) := (decode ro.body : Option Body) | return []
  let some (_, sk, epOp) := eps.find? (·.1 = to) | return []
  let ok ← ((trusts c to frm).liftL : View F Bool).run
  if !ok then return []
  let some addr ← arrivedFrom r | return []
  let f ← Fresh.fresh
  let some co := Reply.op K r sk frm m1 f | return []
  let eo := Eph.op f co.id
  return [co, eo, Established.op co.id r eo.id epOp, Send.op addr co]

def answerAll (K : Keys) (eps : List (B × B × Id)) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (_, .opened r c frm _ _) :: t => do
    let a ← answerOne K eps r c frm
    let b ← answerAll K eps t
    return a ++ b
  | _ :: t => answerAll K eps t

/-- establish, for request r with this side's ephemeral e: each of its
connections with no `established` gets this side's. -/
def establishConns (r e epOp : Id) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (cid, _) :: t => do
    let n ← count established.byConn [cid]
    let rest ← establishConns r e epOp t
    return if n = 0 then Established.op cid r e epOp :: rest else rest

def establishReqs (epOp : Id) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (r, _) :: t => do
    let here ← do
      match ← rows eph.byOf [r] with
      | (e, _) :: _ => establishConns r e epOp (← rows connection.byRequest [r])
      | [] => pure []
    let rest ← establishReqs epOp t
    return here ++ rest

def establishAll : List (B × B × Id) → m (List Op)
  | [] => pure []
  | (pk, _, epOp) :: t => do
    let a ← establishReqs epOp (← rows request.byFrm [pk])
    let b ← establishAll t
    return a ++ b

def react (fam : Family F) (K : Keys) : m (List Op) := do
  let eps ← endpoints
  let opens ← rows opened.all []
  let o1 ← openAll eps
  let o2 ← deliverAll fam opens
  let o3 ← answerAll K eps opens
  let o4 ← establishAll eps
  return o1 ++ o2 ++ o3 ++ o4

/-- The hello a request of this node's sealed (community, address, op
bytes), recovered from its own message 1 with its ephemeral (`sent1`,
as `established` does). -/
def helloOf (K : Keys) (sk : B) (r to m1 : B) : m (Option (B × B × List B)) := do
  match ← rows eph.byOf [r] with
  | (_, .eph _ _ e) :: _ =>
    return (Noise.sent1 K.suite prologue sk e to m1).bind fun (_, p1) =>
      (decode p1 : Option (B × B × List B))
  | _ => return none

/-- Whether a hello delivers the op `req`. -/
def delivers (req : Id) : Option (B × B × List B) → Bool
  | some (_, _, ops) => ops.any fun b => (Op.decode b).any (·.id == req)
  | none => false

/-- Of these requests of this node's, the one to `inviter` whose hello
delivers the join request `req`: the request a pending join is sent as. -/
def requestOf (K : Keys) (sk inviter : B) (req : Id) : List (Id × Fact) → m (Option Id)
  | [] => pure none
  | (r, .request t _ m1) :: rest => do
    if t = inviter then
      let h ← helloOf K sk r inviter m1
      if delivers req h then return some r
    requestOf K sk inviter req rest
  | _ :: rest => requestOf K sk inviter req rest

/-- Whether this node holds a session with the node whose key is `peer`. -/
def connectedTo (peer : B) : m Bool := do
  return (← rows established.all []).any fun (_, f) => match f with
    | .established _ _ p .. => decide (p = peer)
    | _ => false

/-- What a tick sends for one pending join of community c, by device d,
to the inviter's key at the link's first hint, if this node is in c as d
(`mine`: a join stopped waiting on is not, nor a cut device's):
- **waiting** (d not admitted here): the request whose hello delivers
  this join's request, resent, or composed if this node holds none,
  until a connection answers it, beside an open session or not (a
  session may be open for other communities, or carry c's old ops after
  a removal: the inviter takes a new device's request only bare);
- **admitted**: the same, while no session to the inviter is open, so a
  dropped session is dialed again. -/
def dialOne (K : Keys) (listen pk sk : B) : Community.Fact → m (List Op)
  | .joining c inviter hints req _ d _ => do
    let some hint := hints.head? | return []
    let some (me, _) ← ((Community.mine c).liftL : View F _).run | return []
    if me ≠ d then return []
    let adm : Answer F ← Lists.list (m := m) (Community.admission.byDevice.query [c, d] (limit := some 0))
    let r? ← requestOf K sk inviter req (← rows request.byFrm [pk])
    let skip ← if adm.total ≠ 0 then connectedTo inviter else
      match r? with
      | some r => do
        let n ← count connection.byRequest [r]
        pure (decide (n ≠ 0))
      | none => pure false
    if skip then return []
    match r? with
    | some r =>
      let ro ← Store.getOp (m := m) r
      return match ro with
        | some ro => [Send.op hint ro]
        | none => []
    | none =>
      let some jr ← Store.getOp (m := m) req | return []
      let e ← Fresh.fresh
      return match Request.op K sk inviter e (hello c listen [jr]) with
        | some ro => [ro, Eph.op e ro.id, Send.op hint ro]
        | none => []
  | _ => return []

def dialAll (K : Keys) (listen pk sk : B) : List (Pos × Community.Fact) → m (List Op)
  | [] => pure []
  | (_, f) :: rest => do
    let a ← dialOne K listen pk sk f
    let b ← dialAll K listen pk sk rest
    return a ++ b

/-- `listen` is this node's own address, put in its hellos; each pending
join is dialed as `dialOne` says, from this node's key. -/
def dial (K : Keys) (listen : B) (_now : Nat) : m (List Op) := do
  let some (pk, sk, _) := (← endpoints).head? | return []
  let joins : Answer F ← Lists.list (m := m) (Community.joining.all.query [])
  dialAll K listen pk sk joins.lefts

/-- What closing connection cid purges: the connection and the request
it answers. Purge takes every dependent with them: the ephemerals, the
opened and established ops, the couriers and the
arrival records. -/
def closing (cid : Id) : m (List Id) := do
  let some co ← Store.getOp (m := m) cid | return []
  return cid :: co.reqs

/-- What connection cid carries now (`roomsV`): rooms synced, and
notices to give. -/
def rooms (cid : Id) : m (List Room) := (roomsV cid).run

/-- What a step's status writes: a notice given on cid is recorded
(`conn.given`), so the rooms view stops carrying it; a room's settle
writes nothing. -/
def settled (cid : Id) : Status → List Op
  | .given x => [Given.op cid x]
  | .settled _ => []

/-- When and from where op x first arrived bare, if it did. -/
def arrival (x : Id) : m (Option (B × Nat)) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a t => some (a, t)
    | _ => none

/-- The established session of this fact: its id, the peer, whether
this side dialed, and the address and time its handshake arrived here
(the connection, for the dialer; the request, for the responder). -/
def sessionOf : Fact → m (Option (Id × B × Bool × B × Nat))
  | .established cid _ peer _ _ _ dialer => do
    let x ← if dialer then pure cid
      else pure ((← Store.getOp (m := m) cid).map (·.reqs.headD .empty) |>.getD cid)
    let at_ ← arrival x
    return at_.map fun (a, t) => (cid, peer, dialer, a, t)
  | _ => return none

def sessionsOf : List (Id × Fact) → m (List (Id × B × Bool × B × Nat))
  | [] => pure []
  | (_, f) :: t => do
    let e ← sessionOf f
    let rest ← sessionsOf t
    return match e with
      | some e => e :: rest
      | none => rest

/-- Every established session (`sessionOf`). -/
def allSessions : m (List (Id × B × Bool × B × Nat)) := do
  return (← sessionsOf (← rows established.all [])).reverse

/-- The sessions kept: one per peer. Per peer and side (this device
dialed, or the peer did), the latest established is kept, since a
redial supersedes the dial it replaces. Of the at most two left, the
smaller id is kept. Both ends hold the same connection ops and see the
same dials in the same order, so they keep the same one with no message
between them. -/
def kept (all : List (Id × B × Bool × B × Nat)) : List Id := Id.run do
  let later (a b : Id × B × Bool × B × Nat) : Bool := a.2.2.2.2 > b.2.2.2.2 || (a.2.2.2.2 == b.2.2.2.2 && lt a.1 b.1)
  let mut best : List (Id × B × Bool × B × Nat) := []
  for s in all do
    match best.find? fun b => b.2.1 == s.2.1 && b.2.2.1 == s.2.2.1 with
    | some b => if later s b then best := s :: best.filter (fun c => c.1 != b.1)
    | none => best := s :: best
  let mut out : List (B × Id) := []
  for s in best do
    match out.find? (·.1 == s.2.1) with
    | some (_, c) => if lt s.1 c then out := (s.2.1, s.1) :: out.filter (·.1 != s.2.1)
    | none => out := (s.2.1, s.1) :: out
  return out.map (·.2)

/-- Of these sessions, those that carry something (`roomsV`): a room or
a notice not yet given. -/
def carrying : List (Id × B × Bool × B × Nat) → m (List (Id × B × Bool × B × Nat))
  | [] => pure []
  | e :: t => do
    let rs ← (roomsV e.1).run
    let rest ← carrying t
    return if rs.isEmpty then rest else e :: rest

/-- The sessions kept open: one per peer (`kept`), while it carries
something. A session that carries nothing (no room the trust rule takes,
no notice owed) is retired, so a removed member's session closes once
its notices are given (`notice_then_cut`). -/
def openSessions : m (List (Id × B × Bool × B × Nat)) := do
  let all ← allSessions
  let k := kept all
  carrying (all.filter fun e => k.contains e.1)

/-- Open sessions (`openSessions`): id, the bare address the handshake
ran on, and whether this side dialed. -/
def sessions : m (List (Id × B × Bool)) := do
  return (← openSessions).map fun (cid, _, dialer, a, _) => (cid, a, dialer)

/-- Sessions not kept open: to be closed and purged. -/
def retired : m (List Id) := do
  let all ← allSessions
  let open_ ← openSessions
  return all.filterMap fun (cid, _) => if open_.any (fun e => decide (e.1 = cid)) then none else some cid

/-- A session's transport keys: send, receive. -/
def sessionKeys (cid : Id) : m (Option (B × B)) := do
  return (← rows established.byConn [cid]).findSome? fun (_, f) => match f with
    | .established _ _ _ _ s r _ => some (s, r)
    | _ => none

/-- These bytes sealed for session cid, with a fresh nonce; none
without the session's keys. -/
def sealFor (K : Keys) (cid : Id) (p : B) : m (Option B) := do
  let some (sk, _) ← sessionKeys cid | return none
  let n := (← Fresh.fresh).extract 0 24
  return some (Frame.seal K cid sk n p)

/-- A sealed frame's session and bytes, if it opens under that
session's receive key. -/
def openFrame (K : Keys) (b : B) : m (Option (Id × B)) := do
  let some cid := Frame.cid b | return none
  let some (_, rk) ← sessionKeys cid | return none
  return Frame.open K rk b

def outbox : m (List (Id × B × B)) := do
  let mut out := []
  for (x, f) in ← rows send.all [] do
    let .send op addr := f | continue
    let some o ← Store.getOp (m := m) op | continue
    out := (x, addr, o.bytes) :: out
  return out.reverse

/-- Couriers carrying these connections back to `addr`. -/
def resendConns (addr : B) : List (Id × Fact) → m (List Op)
  | [] => pure []
  | (cid, _) :: t => do
    let rest ← resendConns addr t
    let co ← Store.getOp (m := m) cid
    return match co with
      | some co => Send.op addr co :: rest
      | none => rest

/-- On every arrival: the first one of an op is recorded, when and how
it came, and a saturated post gets this device's receipt, which orders
it (`Community.receiptFor`). A request that arrives again bare, opened
here for community c from key frm, and still from a peer the trust rule
takes for c, gets its connections resent to where it came from. That is
the healing for a lost answer, as poc-17 has it ("a replayed request is
answered with the identical bytes again"); a removed member's node
replaying its request gets nothing (`resend_trusted`). -/
def onArrival (via : Option Id) (addr : B) (o : Op) (at_ : Nat) : m (List Op) := do
  let n ← count recv.byOp [o.id]
  let first := if n = 0 then [Recv.op o.id via addr at_] else []
  let first := first ++ (← ((Community.receiptFor o).liftL : View F (List Op)).run)
  if via.isSome then return first
  let some (.request to _ _) := (decode o.body : Option Body) | return first
  let some (_, .opened _ c frm _ _) := (← rows opened.byRequest [o.id]).head? | return first
  let ok ← ((trusts c to frm).liftL : View F Bool).run
  if !ok then return first
  let more ← resendConns addr (← rows connection.byRequest [o.id])
  return first ++ more

/-- What the node driver calls. -/
def hooks (fam : Family F) (K : Keys) (listen : B) : Hooks F m where
  rooms := rooms
  settled := settled
  recv := onArrival
  outbox := outbox
  react := react fam K
  dial := dial K listen
  established := sessions
  closing := closing
  retired := retired
  sealFor := sealFor K
  openFrame := openFrame K

end

end Connection
