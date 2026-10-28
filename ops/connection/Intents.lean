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

`dial`, on a tick: for each pending join, this node's request to the
inviter's key is resent on a courier to the link's first hint, or
composed if there is none yet, while no session to the inviter's key is
open, or while one is but the inviter has not let this node into c (its
key is not let in for c here: the inviter carries nothing of c for the
joiner before it approves, so the request goes bare, beside a session
open for other communities). A tick is the retry: lean-net's "the
joiner re-sends the same hello every tick".

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

/-- Of these (community, peer) pairs, the communities where this node
is a device and the trust rule takes the peer, in order. -/
def roomsOf : List (B × B) → View F (List Id)
  | [] => pure []
  | (c, peer) :: rest => do
    let ok ← do
      match ← meV c with
      | some me => ((trusts c me peer).liftL : View F Bool)
      | none => pure false
    let tail ← roomsOf rest
    return if ok then c :: tail else tail

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

/-- The rooms the peer on connection cid may see now, as a view: of the
communities this node holds, each one where this node is a device and
the trust rule takes a peer key cid's established facts name
(`trusts`). A session is one per peer key, and carries every community
both nodes share, whatever its hello named. -/
def roomsV (cid : Id) : View F (List Id) := do
  let a ← View.read (F := F) (established.byConn.query [cid])
  let cs ← heldV
  roomsOf ((peersOf a).flatMap fun peer => cs.map (·, peer))

/-- The rooms and notices settled on connection cid (`conn.settled`). -/
def givenOn (cid : Id) : View F (List Id) := do
  let a ← View.read (F := F) (settled.byConn.query [cid])
  return a.rights.filterMap fun (_, f) => match f with
    | .settled _ r => some r
    | _ => none

/-- What a connection carries for these (community, peer) pairs: the
community, synced, where this node is a device and the trust rule takes
the peer; else a notice of each removal that cuts a device under the
peer's key (`Community.removalsAt`), not yet given on it. -/
def carriedOf (given : List Id) : List (B × B) → View F (List Room)
  | [] => pure []
  | (c, peer) :: rest => do
    let here ← do
      match ← meV c with
      | some me =>
        if ← ((trusts c me peer).liftL : View F Bool) then pure [Room.sync c]
        else
          let xs ← ((Community.removalsAt c peer).liftL : View F (List Id))
          pure ((xs.filter fun x => !has given x).map (Room.notice c))
      | none => pure []
    let tail ← carriedOf given rest
    return here ++ tail

/-- What connection cid carries now, as a view read afresh on every
step. A session is one per peer key, whatever community its hello
named: for each community this node holds, the room synced, or the
notices owed to a removed member's node, or nothing. -/
def carriedV (cid : Id) : View F (List Room) := do
  let a ← View.read (F := F) (established.byConn.query [cid])
  let given ← givenOn cid
  let cs ← heldV
  carriedOf given ((peersOf a).flatMap fun peer => cs.map (·, peer))

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

/-- The community a request of this node's names in its hello, recovered
from its own message 1 with its ephemeral (`sent1`, as `established`
does). -/
def helloOf (K : Keys) (sk : B) (r to m1 : B) : m (Option B) := do
  match ← rows eph.byOf [r] with
  | (_, .eph _ _ e) :: _ =>
    return (Noise.sent1 K.suite prologue sk e to m1).bind fun (_, p1) =>
      (decode p1 : Option (B × B × List B)).map (·.1)
  | _ => return none

/-- Whether this node holds a session with the node whose key is `peer`. -/
def connectedTo (peer : B) : m Bool := do
  return (← rows established.all []).any fun (_, f) => match f with
    | .established _ _ p .. => decide (p = peer)
    | _ => false

/-- `listen` is this node's own address, put in its hellos. Only the
store's own entry for c (`mine`) is dialed; a join this device stopped
waiting on (`abandon`) is not, and neither is a cut device's. -/
def dial (K : Keys) (listen : B) (_now : Nat) : m (List Op) := do
  let some (pk, sk, _) := (← endpoints).head? | return []
  let mut out : Array Op := #[]
  let joins : Answer F ← Lists.list (m := m) (Community.joining.all.query [])
  for (_, f) in joins.lefts do
    let .joining c inviter hints req _ d _ := f | continue
    let some hint := hints.head? | continue
    let some (me, _) ← ((Community.mine c).liftL : View F _).run | continue
    if me ≠ d then continue
    if ← connectedTo inviter then
      if ← ((Community.allowPeer c inviter).liftL : View F Bool).run then continue
    let mut mineTo : Option Id := none
    for (r, g) in ← rows request.byFrm [pk] do
      let .request t _ m1 := g | continue
      if t ≠ inviter then continue
      if (← helloOf K sk r inviter m1) = some c then mineTo := some r
    match mineTo with
    | some r =>
      if let some ro ← Store.getOp (m := m) r then out := out.push (Send.op hint ro)
    | none =>
      let some jr ← Store.getOp (m := m) req | continue
      let e ← Fresh.fresh
      let some ro := Request.op K sk inviter e (hello c listen [jr]) | continue
      out := out ++ #[ro, Eph.op e ro.id, Send.op hint ro]
  return out.toList

/-- What closing connection cid purges: the connection and the request
it answers. Purge takes every dependent with them: the ephemerals, the
opened and established ops, the couriers and the
arrival records. -/
def closing (cid : Id) : m (List Id) := do
  let some co ← Store.getOp (m := m) cid | return []
  return cid :: co.reqs

/-- The rooms the peer on connection cid may see now (`roomsV`). -/
def rooms (cid : Id) : m (List Id) := (roomsV cid).run

/-- When and from where op x first arrived bare, if it did. -/
def arrival (x : Id) : m (Option (B × Nat)) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a t => some (a, t)
    | _ => none

/-- Every established session: its id, the peer, whether this side
dialed, and the address and time its handshake arrived here (the
connection, for the dialer; the request, for the responder). -/
def allSessions : m (List (Id × B × Bool × B × Nat)) := do
  let mut out := []
  for (_, f) in ← rows established.all [] do
    let .established cid _ peer _ _ _ dialer := f | continue
    let x ← if dialer then pure cid
      else pure ((← Store.getOp (m := m) cid).map (·.reqs.headD .empty) |>.getD cid)
    if let some (a, t) ← arrival x then out := (cid, peer, dialer, a, t) :: out
  return out

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

/-- Open sessions, one per peer (`kept`): id, the bare address the
handshake ran on, and whether this side dialed. -/
def sessions : m (List (Id × B × Bool)) := do
  let all ← allSessions
  let k := kept all
  return all.filterMap fun (cid, _, dialer, a, _) => if k.contains cid then some (cid, a, dialer) else none

/-- Sessions no longer kept: to be closed and purged. -/
def retired : m (List Id) := do
  let all ← allSessions
  let k := kept all
  return all.filterMap fun (cid, _) => if k.contains cid then none else some cid

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
it came. A request that arrives again bare, opened here for community c
from key frm, and still from a peer the trust rule takes for c, gets its
connections resent to where it came from. That is the healing for a
lost answer, as poc-17 has it ("a replayed request is answered with the
identical bytes again"); a removed member's node replaying its request
gets nothing (`resend_trusted`). -/
def onArrival (via : Option Id) (addr : B) (o : Op) (at_ : Nat) : m (List Op) := do
  let n ← count recv.byOp [o.id]
  let first := if n = 0 then [Recv.op o.id via addr at_] else []
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
