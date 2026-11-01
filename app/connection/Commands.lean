import engine.wire.Node
import engine.wire.Winner
import app.connection.Family
import app.connection.eph.Commands
import app.connection.established.Commands
import app.connection.opened.Commands
import app.connection.recv.Commands
import engine.sync.Notice

namespace Connection
open Engine Engine.Sync Codec

instance [Codec F] [SortKey F] : Fresh (SqlM F) := ⟨Noise.randomBytes 32⟩

/-- The notices given on connection cid (`conn.given`). -/
def givenOn (cid : Id) : View F (List Id) := do
  let a ← View.read (F := F) (given.byConn.query [cid])
  return a.rights.filterMap fun (_, f) => match f with
    | .given _ x => some x
    | _ => none
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- Byte order on ids. -/
def lt (a b : B) : Bool := a.toList < b.toList

def openAll : List (B × B × Id) → m (List Op)
  | [] => pure []
  | (pk, _, epOp) :: t => do
    let a ← openEach epOp (← rows request.byTo [pk])
    let b ← openAll t
    return a ++ b

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

/-- The sessions kept: one per peer, the one with the least connection
id (`Winner.select`). Both ends hold the same connection ops, so they keep
the same one with no message between them, whatever order the dials
arrived in, whichever side dialed, and whatever their clocks say
(`both_choose_same`); a later dial never displaces a lower live id. -/
def kept (all : List (Id × B × Bool × B × Nat)) : List Id :=
  (Winner.select (all.map fun s => (s.1, s.2.1))).map (·.2)

/-- A session's transport keys: send, receive. -/
def sessionKeys (cid : Id) : m (Option (B × B)) := do
  return (← rows established.byConn [cid]).findSome? fun (_, f) => match f with
    | .established _ _ _ _ s r _ => some (s, r)
    | _ => none
end
open Engine

def Frame.version : UInt8 := 1

def Frame.ad (cid : Id) : B := ⟨#[Frame.version]⟩ ++ cid

/-- Bytes sealed for connection cid with send key `sk` and nonce `n`. -/
def Frame.seal (K : Keys) (cid sk n p : B) : B := ⟨#[Frame.version]⟩ ++ cid ++ n ++ K.fenc sk n (Frame.ad cid) p
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- These bytes sealed for session cid, with a fresh nonce; none
without the session's keys. -/
def sealFor (K : Keys) (cid : Id) (p : B) : m (Option B) := do
  let some (sk, _) ← sessionKeys cid | return none
  let n := (← Fresh.fresh).extract 0 24
  return some (Frame.seal K cid sk n p)
end
open Engine

/-- A frame's connection id, if it is one. -/
def Frame.cid (b : B) : Option Id :=
  if b.size < 73 ∨ b.get! 0 ≠ Frame.version then none else some (b.extract 1 33)

/-- A frame's connection id and bytes, opened with receive key `rk`. -/
def Frame.open (K : Keys) (rk b : B) : Option (Id × B) :=
  if b.size < 73 ∨ b.get! 0 ≠ Frame.version then none else
  let cid := b.extract 1 33
  (K.fdec rk (b.extract 33 57) (Frame.ad cid) (b.extract 57 b.size)).map (cid, ·)
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- A sealed frame's session and bytes, if it opens under that
session's receive key. -/
def openFrame (K : Keys) (b : B) : m (Option (Id × B)) := do
  let some cid := Frame.cid b | return none
  let some (_, rk) ← sessionKeys cid | return none
  return Frame.open K rk b

end
end Connection
