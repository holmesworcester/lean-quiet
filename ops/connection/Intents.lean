/-
The connection family's reactions and commands: views over lists that
return the ops to write. The node runs `react` after every write and
`dial` on every tick, and writes what they return. Nothing here sends
anything, or decides anything outside ops.

`react`, for this device:
- **open**: every request to its key with no `opened` gets one.
- **deliver**: an opened request's hello ops of its community go to the
  writer, if not yet stored. This is how a joiner's request reaches the
  members.
- **answer**: an opened request with no connection, whose initiator the
  trust rule admits for the hello's community, gets an ephemeral, the
  connection, this side's `established`, and a courier back to the
  address the request arrived from. A request the rule does not admit
  gets nothing, so the request opens nothing.
- **establish**: a connection answering one of this device's requests,
  with no `established`, gets this side's.

`dial`, on a tick: for each pending join with no session to its
inviter, this device's request to the inviter is resent on a courier to
the link's first hint, or composed if there is none yet. A tick is the
retry: it is lean-net's "the joiner re-sends the same hello every tick".

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

namespace Connection
open Engine Engine.Sync Codec

/-- The trust rule (lean-net's): `peer` is a live member of c by this
node's ops; or, before this device (`me`) is admitted, `peer` is the
inviter its pending join names and its ops know nothing of `peer` yet. -/
def trusts (c me peer : B) : View Community.Fact Bool := do
  if ← Community.allowPeer c peer then return true
  let joins ← Community.joining.all.read []
  let linked := joins.rows.any fun (_, f) => match f with
    | .joining c' k _ _ _ _ _ => decide (c' = c ∧ k = peer)
    | _ => false
  if !linked then return false
  let admitted ← Community.allowPeer c me
  let known ← Community.admission.byDevice.read [c, peer] (limit := some 0)
  return !admitted && known.total = 0

instance [Codec F] [SortKey F] : Fresh (SqlM F) := ⟨Noise.randomBytes 32⟩

/-- The device this node is in community c as (`Community.mine`), if it
holds that device's secret. -/
def meV (c : B) : View F (Option B) := do
  let some (d, _) ← ((Community.mine c).liftL : View F _) | return none
  let a ← View.read (F := F) (Community.secret.all.query [])
  let held := a.lefts.any fun (_, f) => match f with
    | .secret pk _ => decide (pk = d)
    | _ => false
  return if held then some d else none

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

/-- The (community, peer) pairs of connection cid's established facts. -/
def pairsOf (a : Answer F) : List (B × B) :=
  a.rights.filterMap fun (_, f) => match f with
    | .established _ c peer .. => some (c, peer)
    | _ => none

/-- The rooms the peer on connection cid may see now, as a view: each
community one of cid's established facts names, with its peer, where
this node is a device and the trust rule takes the peer (`trusts`). -/
def roomsV (cid : Id) : View F (List Id) := do
  let a ← View.read (F := F) (established.byConn.query [cid])
  return (← roomsOf (pairsOf a)).reverse

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

/-- The devices this node speaks for: every device whose secret it
holds (local `secret` ops), as key, seed and secret op. One node serves
all of them, so joining another community needs no restart. -/
def devices : m (List (B × B × Id)) := do
  let a : Answer F ← Lists.list (m := m) (Community.secret.all.query [])
  return a.lefts.filterMap fun ((_, x), f) => match f with
    | .secret pk seed => some (pk, seed, x)
    | _ => none

/-- The device this node is in community c as (its acceptance of c),
with its seed and secret op. -/
def meIn (c : B) : m (Option (B × B × Id)) := do
  let some (d, _) ← ((Community.mine c).liftL : View F _).run | return none
  return (← devices).find? (·.1 = d)

/-- The bare address op x arrived from, if it arrived bare. -/
def arrivedFrom (x : Id) : m (Option B) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a _ => some a
    | _ => none

def react (fam : Family F) (K : Keys) : m (List Op) := do
  let mine ← devices
  let mut out : Array Op := #[]
  -- open
  for (me, _, secretOp) in mine do
    for (r, _) in ← rows request.byTo [me] do
      if (← count opened.byRequest [r]) = 0 then out := out.push (Opened.op r secretOp)
  -- deliver, and answer the trusted
  for (_, f) in ← rows opened.all [] do
    let .opened r c frm _ ops := f | continue
    for b in ops do
      let some o := Op.decode b | continue
      if decide (fam.scope o = .shared c) && (← Store.getOp (m := m) o.id).isNone then
        out := out.push o
    if (← count connection.byRequest [r]) ≠ 0 then continue
    let some ro ← Store.getOp (m := m) r | continue
    let some (.request me _ m1) := (decode ro.body : Option Body) | continue
    let some (_, seed, secretOp) := mine.find? (·.1 = me) | continue
    if !(← ((trusts c me frm).liftL : View F Bool).run) then continue
    let some addr ← arrivedFrom r | continue
    let f ← Fresh.fresh
    let some co := Reply.op K r seed frm m1 f | continue
    let eo := Eph.op f co.id
    out := out ++ #[co, eo, Established.op co.id r eo.id secretOp, Send.op addr co]
  -- establish
  for (me, _, secretOp) in mine do
    for (r, _) in ← rows request.byFrm [me] do
      for (cid, _) in ← rows connection.byRequest [r] do
        if (← count established.byConn [cid]) ≠ 0 then continue
        match ← rows eph.byOf [r] with
        | (e, _) :: _ => out := out.push (Established.op cid r e secretOp)
        | [] => pure ()
  return out.toList

/-- Whether this device holds a session with `peer`. -/
def connectedTo (peer : B) : m Bool := do
  return (← rows established.all []).any fun (_, f) => match f with
    | .established _ _ p .. => decide (p = peer)
    | _ => false

/-- `listen` is this node's own address, put in its hellos. A join this
device stopped waiting on (`abandon`) is not dialed. -/
def dial (K : Keys) (listen : B) (_now : Nat) : m (List Op) := do
  let mut out : Array Op := #[]
  let joins : Answer F ← Lists.list (m := m) (Community.joining.all.query [])
  for (_, f) in joins.lefts do
    let .joining c inviter hints req _ d _ := f | continue
    let some hint := hints.head? | continue
    -- only the store's own entry for c (`mine`), and only while waiting on it
    let some (me, seed, _) ← meIn c | continue
    if me ≠ d then continue
    if ← connectedTo inviter then continue
    let mineTo := (← rows request.byFrm [me]).find? fun (_, g) => match g with
      | .request t _ _ => decide (t = inviter)
      | _ => false
    match mineTo with
    | some (r, _) =>
      if let some ro ← Store.getOp (m := m) r then out := out.push (Send.op hint ro)
    | none =>
      let some jr ← Store.getOp (m := m) req | continue
      let e ← Fresh.fresh
      let some ro := Request.op K seed inviter e (hello c listen [jr]) | continue
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

/-- On every arrival: the first one of an op is recorded, when and
how it came. A request that arrives again, already answered by this
device, gets its connection resent to where it came from. That is the
healing for a lost answer, as poc-17 has it ("a replayed request is
answered with the identical bytes again"). -/
def onArrival (via : Option Id) (addr : B) (o : Op) (at_ : Nat) : m (List Op) := do
  let first := if (← count recv.byOp [o.id]) = 0 then [Recv.op o.id via addr at_] else []
  if via.isSome then return first
  let resend ← do
    match (decode o.body : Option Body) with
    | some (.request ..) =>
      let mut out := []
      for (cid, _) in ← rows connection.byRequest [o.id] do
        if (← count opened.byRequest [o.id]) ≠ 0 then
          if let some co ← Store.getOp (m := m) cid then out := Send.op addr co :: out
      pure out
    | _ => pure []
  return first ++ resend

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
