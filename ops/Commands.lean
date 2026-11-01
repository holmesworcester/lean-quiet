import engine.wire.Node
import ops.community.member.invite.request.Commands
import ops.community.member.join.joining.Commands
import ops.connection.Commands
import ops.connection.Family
import ops.connection.connection.Commands
import ops.connection.eph.Commands
import ops.connection.established.Commands
import ops.connection.given.Commands
import ops.connection.opened.Commands
import ops.connection.recv.Commands
import ops.connection.request.Commands
import ops.connection.send.Commands
import engine.sync.Notice

/-!
`app`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Connection
open Engine Engine.Sync Codec

/-- The communities this node has accepted, each once: the ones a
session may carry. -/
def heldV : View F (List B) := do
  let a ← View.read (F := F) (Community.accepted.all.query [])
  return (a.lefts.filterMap fun (_, f) => match f with
    | .accepted c _ => some c
    | _ => none).eraseDups

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
end Connection
namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- This node's keys: each endpoint op's public key, secret and id (one,
the first `found` or `join` writes it). -/
def endpoints : m (List (B × B × Id)) := do
  let a : Answer F ← Lists.list (m := m) (Community.endpoint.all.query [])
  return a.lefts.filterMap fun ((_, x), f) => match f with
    | .endpoint pk sk => some (pk, sk, x)
    | _ => none

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

def react (fam : Family F) (K : Keys) : m (List Op) := do
  let eps ← endpoints
  let opens ← rows opened.all []
  let o1 ← openAll eps
  let o2 ← deliverAll fam opens
  let o3 ← answerAll K eps opens
  let o4 ← establishAll eps
  return o1 ++ o2 ++ o3 ++ o4

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
  onGiven := onGiven
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
