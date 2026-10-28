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

`closing cid`: what a closed session purges: the connection, its
request and this side's ephemeral. Purge takes their dependents with
them (opened, established, settled, arrivals) and the couriers routed
to cid.

They run in any monad that reads lists and ops and gives fresh
secrets: the node's SQLite monad, with the OS's random bytes, or the
engine's model, so the same code runs in proofs by induction over a
world of nodes.
-/
import Connection.Family
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
    let eo := Eph.op f
    out := out ++ #[eo, co, Established.op co.id r eo.id secretOp, Send.op (.bare addr) co.bytes]
  -- establish
  for (r, f) in ← rows request.byFrm [me] do
    let .request _ _ m1 := f | continue
    for (cid, _) in ← rows connection.byRequest [r] do
      if (← count established.byConn [cid]) ≠ 0 then continue
      match ← rows eph.byPub [m1.extract 0 32] with
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
      if let some ro ← Store.getOp (m := m) r then out := out.push (Send.op (.bare hint) ro.bytes)
    | none =>
      let some jr ← Store.getOp (m := m) req | continue
      let e ← Fresh.fresh
      let some ro := Request.op K seed inviter e (hello c listen [jr]) | continue
      out := out ++ #[Eph.op e, ro, Send.op (.bare hint) ro.bytes]
  return out.toList

/-- What closing connection cid purges (with their dependents). -/
def closing (cid : Id) : m (List Id) := do
  let some co ← Store.getOp (m := m) cid | return []
  let ests ← rows established.byConn [cid]
  let mut ids := [cid] ++ co.reqs
  for (x, _) in ests do
    if let some eo ← Store.getOp (m := m) x then ids := ids ++ (eo.reqs.drop 2).take 1
  let couriers := (← rows send.all []).filterMap fun (x, g) => match g with
    | .send false d _ => if d = cid then some x else none
    | _ => none
  return ids ++ couriers

/-- The rooms the peer on connection cid may see now. -/
def rooms (seed : B) (cid : Id) : m (List Id) := do
  let some (me, _) ← mine seed | return []
  let mut out := []
  for (_, f) in ← rows established.byConn [cid] do
    let .established _ c peer .. := f | continue
    if ← ((trusts c me peer).liftL : View F Bool).run then out := c :: out
  return out

/-- Open sessions: id, the bare address the handshake ran on, and
whether this side dialed. -/
def sessions : m (List (Id × B × Bool)) := do
  let mut out := []
  for (_, f) in ← rows established.all [] do
    let .established cid _ _ _ _ _ dialer := f | continue
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

def outbox : m (List (Id × Route × B)) := do
  return (← rows send.all []).filterMap fun (x, f) => match f with
    | .send true d b => some (x, .bare d, b)
    | .send false d b => some (x, .conn d, b)
    | _ => none

end

/-- What the node driver calls. -/
def hooks (fam : Family F) (K : Keys) (seed listen : B) : Hooks F where
  rooms := rooms seed
  settled cid room := [Settled.op cid room]
  recv via addr o at_ := [Recv.op o.id via addr at_]
  outbox := outbox
  react := react fam K seed
  dial := dial K seed listen

end Connection
