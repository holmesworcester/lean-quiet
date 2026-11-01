/- Discovery policy on the running op engine. All durable changes, including
retry clocks and scan cursors, are ops returned to the node's writer. Native
interface/DNS-SD workers only submit bounded local discovery observations. -/
import ops.connection.Intents

namespace Connection.Discovery
open Engine Engine.Sync Codec

/-- Four candidate rows per tick: two invites first, then two memberships.
Each can emit at most one courier and is subject to its peer's retry clock. -/
def pageSize : Nat := 2

def readCommunity (r : Rel Community.Fact) (args : List B) (limit : Nat := 1)
    (after : Option Pos := none) (desc : Bool := true) : View F (List (Pos × Community.Fact)) := do
  let a ← View.read (F := F) (r.query args (some limit) desc after (cap := limit))
  return a.lefts

def latest (r : Rel Community.Fact) (args : List B) : View F (Option Community.Fact) := do
  return (← readCommunity r args).head?.map (·.2)

/-- Newest advertisement supersedes older ones even when it has expired.
Expiry must never resurrect an old address. -/
def advertised (c peer : B) (now : Nat) : View F (List B) := do
  match ← latest Community.addresses.byPeer [c, peer] with
  | some (.addresses _ _ ds os issued expires) =>
    return if Endpoint.fresh now issued expires then ds ++ os else []
  | _ => return []

def discovered (peer : B) (now : Nat) : View F (List B) := do
  match ← latest Community.discovered.byPeer [peer] with
  | some (.discovered _ hs issued ttl) =>
    return if Endpoint.fresh now issued (issued + ttl) then hs else []
  | _ => return []

def retryState (peer : B) : View F (Option (Nat × Nat)) := do
  match ← latest Community.retry.byPeer [peer] with
  | some (.retry _ time attempts) => return some (time, attempts)
  | _ => return none

/-- Include each source in a bounded round-robin. Invite addresses occupy the
first positions; all eight addresses from each source remain eligible. -/
def candidates (invite published found : List B) : List B :=
  ((invite.take Endpoint.cap ++ published.take Endpoint.cap ++ found.take Endpoint.cap).filter
    (fun b => (Endpoint.parse b).isSome)).eraseDups.take Endpoint.dialCap

def canTry (now : Nat) : Option (Nat × Nat) → Bool
  | none => true
  | some (time, attempts) => Endpoint.due now time attempts

def nextAttempt : Option (Nat × Nat) → Nat
  | none => 0
  | some (_, attempts) => (attempts + 1) % (2^63)

section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- Return a single chosen destination and the op recording the attempt.
The retry clock is per identity, not per advertisement or IP. -/
def plan (c peer : B) (invite : List B) (now : Nat) : m (Option (B × Op)) := do
  let old ← (retryState peer).run
  if !canTry now old then return none
  let hs := candidates invite (← (advertised c peer now).run) (← (discovered peer now).run)
  let attempt := nextAttempt old
  let some addr := Endpoint.pick hs attempt | return none
  return some (addr, Community.mkOp [] (.retry peer now attempt))

def joinOne (K : Keys) (listen pk sk : B) (now : Nat) (f : Community.Fact) : m (List Op) := do
  let .joining c peer hs req name device epoch := f | return []
  let some (addr, retry) ← plan c peer hs now | return []
  let ops ← dialOne K listen pk sk (.joining c peer [addr] req name device epoch)
  return if ops.isEmpty then [] else retry :: ops

/-- Only a held signing secret can author an endpoint op. The validator
independently checks the admission binding and signature. -/
def signer (device : B) : m (Option Community.Device) := do
  match ← (latest Community.secret.byKey [device]).run with
  | some (.secret _ seed) => return some (Community.Device.ofSeed seed)
  | _ => return none

def publish (c adm device pk : B) (now : Nat) : m (List Op) := do
  let some d ← signer device | return []
  if !(← ((Community.deviceLive c device).liftL : View F Bool).run) then return []
  match ← (latest Community.addresses.byPeer [c, pk]).run with
  | some (.addresses _ _ _ _ time _) => if now < time + 60000 then return []
  | _ => pure ()
  let ds ← (discovered pk now).run
  let sightings ← (readCommunity Community.sighting.byTarget [c, pk] 8).run
  let mut os := []
  for (_, f) in sightings do
    let .sighting _ reporter _ addr time := f | continue
    if Endpoint.fresh now time (time + Endpoint.maxAge) && reporter != pk then
      if ← ((Community.allowPeer c reporter).liftL : View F Bool).run then
        os := addr :: os
  let ds := Endpoint.bounded ds |>.take 4
  os := Endpoint.bounded os |>.take 4
  let reqs := [c, adm]
  let b : Community.Body := .addresses ds os now (now + Endpoint.maxAge) .empty
  return [Community.mkOp reqs (.addresses ds os now (now + Endpoint.maxAge)
    (Community.sig d.sk reqs b))]

def remotePort (cid : Id) : m (Option UInt16) := do
  let some co ← Store.getOp (m := m) cid | return none
  let req := co.reqs.headD .empty
  let opened := (← rows Connection.opened.byRequest [req]).head?
  return opened.bind fun (_, f) => match f with
    | .opened _ _ _ addr _ => (Endpoint.parse addr).map (·.2)
    | _ => none

/-- Report the peer's observed IP with its authenticated listening port.
The remote TCP source port on an accepted socket is ephemeral and never
advertised as a listening port. Reports are signed hints, not reachability
certificates; the owner republishes them under the same eight-address cap. -/
def observe (c pk peer : B) (now : Nat) : m (List Op) := do
  match ← (latest Community.sighting.byReporter [c, pk, peer]).run with
  | some (.sighting _ _ _ _ time) => if now < time + 60000 then return []
  | _ => pure ()
  let some (device, _) ← ((Community.mine c).liftL : View F _).run | return []
  let some d ← signer device | return []
  let some ((_, adm), _) := (← (readCommunity Community.admission.byDevice [c, device]).run).head?
    | return []
  let a : Answer F ← Lists.list (m := m) (established.byPeer.query [peer] (some 1) (cap := 1))
  let some (_, f) := a.rights.head? | return []
  let some (cid, _, dialer, actual, _) ← sessionOf f | return []
  let some (host, port) := Endpoint.parse actual | return []
  let listening ← if dialer then pure (some port) else remotePort cid
  let some port := listening | return []
  let addr := (toString host ++ ":" ++ toString port).toUTF8
  let reqs := [c, adm]
  let b : Community.Body := .sighting peer addr now .empty
  return [Community.mkOp reqs (.sighting peer addr now (Community.sig d.sk reqs b))]

/-- Reuse the same handshake bytes until answered. An advertisement never
forces replacement of an established session (the POC-7 bootstrap race). -/
def memberOne (K : Keys) (listen pk sk : B) (now : Nat) (adm : Id) (f : Community.Fact) : m (List Op) := do
  let .admission c _ device peer := f | return []
  if peer == pk then return ← publish c adm device pk now
  let ok ← ((Community.allowPeer c peer).liftL : View F Bool).run
  let mine ← ((Community.allowPeer c pk).liftL : View F Bool).run
  if !ok || !mine then return []
  if ← connectedTo peer then return ← observe c pk peer now
  let some (addr, retry) ← plan c peer [] now | return []
  let a : Answer F ← Lists.list (m := m) (request.byTo.query [peer] (limit := some 8) (cap := 8))
  for ((_, rid), fact) in a.rights do
    let .request _ frm _ := fact | continue
    if frm != pk then continue
    if let some ro ← Store.getOp (m := m) rid then
      return [retry, Send.op addr ro]
  let e ← Fresh.fresh
  let some ro := Request.op K sk peer e (hello c listen []) | return []
  return [retry, ro, Eph.op e ro.id, Send.op addr ro]

/-- Cursor pages are capped at the query, not after fetching the history. -/
def page (r : Rel Community.Fact) (cursor : Option Pos) : m (List (Pos × Community.Fact)) := do
  let xs ← (readCommunity r [] pageSize cursor false).run
  if xs.isEmpty && cursor.isSome then
    (readCommunity r [] pageSize none false).run
  else return xs

def dial (K : Keys) (listen : B) (wallBase monoBase now : Nat) : m (List Op) := do
  let some (pk, sk, _) := (← endpoints).head? | return []
  let wall := wallBase + (now - monoBase)
  let cursor ← (latest Community.endpointScan.all []).run
  let (jc, mc) := match cursor with
    | some (.endpointScan b _) => (decode b : Option (Option Pos × Option Pos)).getD (none, none)
    | _ => (none, none)
  let joins ← page Community.joining.all jc
  let members ← page Community.discoveryMembers mc
  let mut ops := []
  for (_, f) in joins do ops := ops ++ (← joinOne K listen pk sk wall f)
  for ((_, adm), f) in members do ops := ops ++ (← memberOne K listen pk sk wall adm f)
  let pos := encode (joins.getLast?.map (·.1), members.getLast?.map (·.1))
  if joins.isEmpty && members.isEmpty then return ops
  if cursor.any (fun f => match f with | .endpointScan b _ => b == pos | _ => false) then return ops
  return Community.mkOp [] (.endpointScan pos wall) :: ops

end

/-- The application and real-network harness use this hook, retaining all
other authenticated handshake, retirement and synchronization handlers. -/
def hooks {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]
    (fam : Family F) (K : Keys) (listen : B) (wallBase monoBase : Nat) : Hooks F m :=
  { Connection.hooks fam K listen with dial := dial K listen wallBase monoBase }

end Connection.Discovery
