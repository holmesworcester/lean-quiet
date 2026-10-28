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
import Connection.Family
import Connection.Frame
import Engine.Sync.Node

namespace Connection
open Engine Engine.Sync Codec

/-- The trust rule (lean-net's): `peer` is a live member of c by this
node's ops; or, before this device (`me`) is admitted, `peer` is the
inviter its pending join names and its ops know nothing of `peer` yet. -/
def trusts (c me peer : B) : View Community.Fact Bool := do
  if ← Community.allowPeer c peer then return true
  let joins ← Community.joining.all.read []
  let linked := joins.rows.any fun (_, f) => match f with
    | .joining c' k _ _ _ => decide (c' = c ∧ k = peer)
    | _ => false
  if !linked then return false
  let admitted ← Community.allowPeer c me
  let known ← Community.admission.byDevice.read [c, peer] (limit := some 0)
  return !admitted && known.total = 0

instance [Codec F] [SortKey F] : Fresh (SqlM F) := ⟨Noise.randomBytes 32⟩

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

/-- This device, if its secret is stored: its key and its secret op. -/
def mine (seed : B) : m (Option (B × Id)) := do
  let ed := Community.ed25519.pub seed
  let a : Answer F ← Lists.list (m := m) (Community.secret.byKey.query [ed])
  return a.lefts.head?.map fun ((_, x), _) => (ed, x)

/-- The bare address op x arrived from, if it arrived bare. -/
def arrivedFrom (x : Id) : m (Option B) := do
  return (← rows recv.byOp [x]).findSome? fun (_, f) => match f with
    | .recv _ false _ a _ => some a
    | _ => none

def react (fam : Family F) (K : Keys) (seed : B) : m (List Op) := do
  let some (me, secretOp) ← mine seed | return []
  let mut out : Array Op := #[]
  -- open
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
    if !(← ((trusts c me frm).liftL : View F Bool).run) then continue
    let some ro ← Store.getOp (m := m) r | continue
    let some (.request _ _ m1) := (decode ro.body : Option Body) | continue
    let some addr ← arrivedFrom r | continue
    let f ← Fresh.fresh
    let some co := Reply.op K r seed frm m1 f | continue
    let eo := Eph.op f co.id
    out := out ++ #[co, eo, Established.op co.id r eo.id secretOp, Send.op (.bare addr) co]
  -- establish
  for (r, f) in ← rows request.byFrm [me] do
    let .request _ _ m1 := f | continue
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

/-- `listen` is this device's own address, put in its hellos. -/
def dial (K : Keys) (seed listen : B) (_now : Nat) : m (List Op) := do
  let some (me, _) ← mine seed | return []
  let mut out : Array Op := #[]
  let joins : Answer F ← Lists.list (m := m) (Community.joining.all.query [])
  for (_, f) in joins.lefts do
    let .joining c inviter hints req _ := f | continue
    let some hint := hints.head? | continue
    if ← connectedTo inviter then continue
    let mineTo := (← rows request.byFrm [me]).find? fun (_, g) => match g with
      | .request t _ _ => decide (t = inviter)
      | _ => false
    match mineTo with
    | some (r, _) =>
      if let some ro ← Store.getOp (m := m) r then out := out.push (Send.op (.bare hint) ro)
    | none =>
      let some jr ← Store.getOp (m := m) req | continue
      let e ← Fresh.fresh
      let some ro := Request.op K seed inviter e (hello c listen [jr]) | continue
      out := out ++ #[ro, Eph.op e ro.id, Send.op (.bare hint) ro]
  return out.toList

/-- What closing connection cid purges: the connection and the request
it answers. Purge takes every dependent with them: the ephemerals, the
opened and established ops, the couriers and the
arrival records. -/
def closing (cid : Id) : m (List Id) := do
  let some co ← Store.getOp (m := m) cid | return []
  return cid :: co.reqs

/-- The rooms the peer on connection cid may see now. -/
def rooms (seed : B) (cid : Id) : m (List Id) := do
  let some (me, _) ← mine seed | return []
  let mut out := []
  for (_, f) in ← rows established.byConn [cid] do
    let .established _ c peer .. := f | continue
    if ← ((trusts c me peer).liftL : View F Bool).run then out := c :: out
  return out

/-- Open sessions: id, the bare address the handshake ran on, and
whether this side dialed. One per peer: if two devices dialed each
other at once, both ends keep the session with the smaller connection
id. Both hold the same connection ops, so they make the same choice
with no message between them. -/
def sessions : m (List (Id × B × Bool)) := do
  let mut best : List (B × Id × Bool) := []
  for (_, f) in ← rows established.all [] do
    let .established cid _ peer _ _ _ dialer := f | continue
    match best.find? (·.1 = peer) with
    | some (_, c, _) => if lt cid c then best := best.map fun b => if b.1 = peer then (peer, cid, dialer) else b
    | none => best := (peer, cid, dialer) :: best
  let mut out := []
  for (_, cid, dialer) in best do
    -- the dialer heard the connection arrive; the responder, its request
    let x ← if dialer then pure cid
      else pure ((← Store.getOp (m := m) cid).map (·.reqs.headD .empty) |>.getD cid)
    if let some a ← arrivedFrom x then out := (cid, a, dialer) :: out
  return out

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

def outbox : m (List (Id × Route × B)) := do
  let mut out := []
  for (x, f) in ← rows send.all [] do
    let .send op bare d := f | continue
    let some o ← Store.getOp (m := m) op | continue
    out := (x, if bare then Route.bare d else Route.conn d, o.bytes) :: out
  return out.reverse

end

/-- A session's sealer. Each frame is its counter (8 bytes, big-endian)
then the sealed bytes, with the counter as Noise's nonce: the send key's
for frames out, the receive key's for frames in. A frame opens only if
its counter is at least the next one expected, so a replayed or
reordered-back frame is refused and a lost one costs nothing. The state
is the two keys and the two counters. -/
def sealer (S : Noise.Suite) (sk rk : B) : Sealer where
  state := encode (sk, (0 : Nat), rk, (0 : Nat))
  sealFrame st p :=
    match (decode st : Option (B × Nat × B × Nat)) with
    | some (k, n, r, m) => (encode (k, n + 1, r, m), Community.be64 n ++ S.enc k n.toUInt64 .empty p)
    | none => (st, .empty)
  openFrame st c :=
    match (decode st : Option (B × Nat × B × Nat)) with
    | some (k, n, r, m) =>
      if c.size < 24 then none else
      let i := (c.extract 0 8).foldl (fun a b => a * 256 + b.toNat) 0
      if i < m ∨ i ≥ 2 ^ 64 - 1 then none else
      (S.dec r i.toUInt64 .empty (c.extract 8 c.size)).map fun p => (encode (k, n, r, i + 1), p)
    | none => none

/-- What the node driver calls. -/
def hooks (fam : Family F) (K : Keys) (seed listen : B) : Hooks F where
  rooms := rooms seed
  recv via addr o at_ := [Recv.op o.id via addr at_]
  outbox := outbox
  react := react fam K seed
  dial := dial K seed listen
  established := sessions
  session cid := do return (← sessionKeys cid).map fun (sk, rk) => sealer K.suite sk rk

end Connection
