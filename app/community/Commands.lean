import app.community.Family
import app.community.channel.message.receipt.Commands
import app.community.device.endpoint.Commands
import app.community.device.secret.Commands
import app.community.key.Commands
import app.community.key.wrap.Commands
import app.community.member.invite.Commands
import app.community.member.invite.request.Commands
import app.community.member.invite.request.approve.Commands
import app.community.member.invite.request.approve.admit.Commands
import app.community.member.join.accept.Commands
import app.community.member.join.joining.Commands
import app.community.member.join.joining.abandon.Commands
import app.community.member.remove.Commands
import app.community.name.Commands
import app.community.profile.Commands

/-!
`community`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- The root of a community founded by device d on the node with key
`key`: the founder's admission names both, signed by d. -/
def root (d : Device) (key : Key) : Op :=
  mkOp [] (.root d.pk key (sig d.sk [] (.root d.pk key .empty)))
end Community
namespace Community
open Engine

/-- Found a community named `name` from this device's seed, the founder
known as `myName`: this node's key if it has none (from `fresh`), the
device's secret (local), the root (naming the device and the node's
key), the device's acceptance (local), the first name, the founder's
first profile (the root is the founder's admission), and the
community's first content key `k` (local), wrapped to the node's key
with ephemeral secret `esk` (fresh random bytes from the caller, as
`fresh` and `k` are). -/
def found (seed name myName : ByteArray) (time : Nat) (k esk fresh : ByteArray) :
    View Fact Write := do
  let (key, pre) ← nodeKeyOr fresh
  let d := Device.ofSeed seed
  let r := root d key
  pure ⟨pre ++ [secret seed, r, accept r.id d.pk, setName r.id r.id r.id [] 1 d name,
    profile r.id r.id d myName time, contentKey r.id k, wrapKey r.id k esk key]⟩

/-- Invite to c from device d (admitted as `myAdm`): the invitation,
and its link, naming this node's key, with the bearer seed and dial
hints given. None on a node with no key (a node that founded or joined
nothing). -/
def inviteTo (c myAdm : Id) (d : Device) (bearerSeed : ByteArray) (hints : List ByteArray)
    (threshold : Nat := 1) : View Fact (Option (Write × Invite)) := do
  let some (key, _) ← nodeKey | pure none
  let p := issue c myAdm d key bearerSeed hints threshold
  pure (some (⟨[p.1]⟩, p.2))

/-- Join from a link, from the node with key `key`, to be known as
`name`: the device's secret, its request (the one op that travels), its
acceptance of the community, and the pending join (which keeps the name
until admission). -/
def joinOps (i : Invite) (seed name : ByteArray) (key : Key) : Write :=
  let d := Device.ofSeed seed
  let req := i.request d key
  ⟨[secret seed, req, accept i.community d.pk, joining i req.id name d.pk]⟩

/-- Whether every admission into c among these rows is into a user with
no removal. -/
def unremoved (c : Id) : List (Pos × Fact) → View Fact Bool
  | [] => .pure true
  | (_, .admission c' u _ _) :: t =>
    if c' = c then
      .list (removals c u) fun a => if a.total = 0 then unremoved c t else .pure false
    else unremoved c t
  | _ :: t => unremoved c t

/-- How this store holds device d's acceptance of c: not at all (none)
if it does not hold d's secret, if d is cut, or if d is not admitted and
no join of it is waited on; else whether d is admitted (and so live). -/
def standing (c : Id) (d : Key) (joins : List (Pos × Fact)) : View Fact (Option Bool) :=
  .list (secret.byKey.query [d] (limit := some 0)) fun sec =>
    if sec.total = 0 then .pure none else
    .list (admission.byDevice.query [c, d]) fun adm =>
      if adm.rows.isEmpty then (waiting c d joins).bind fun w => .pure (if w then some false else none)
      else (unremoved c adm.rows).bind fun ok => .pure (if ok then some true else none)

/-- The best held acceptance of c among these rows. -/
def pick (c : Id) (joins : List (Pos × Fact)) : List (Pos × Fact) → View Fact (Option (Key × Id × Bool))
  | [] => .pure none
  | ((_, aid), .accepted c' d) :: t =>
    if c' = c then
      (standing c d joins).bind fun st => (pick c joins t).bind fun rest =>
        .pure (match st, rest with
          | some adm, some b => some (better (d, aid, adm) b)
          | some adm, none => some (d, aid, adm)
          | none, r => r)
    else pick c joins t
  | _ :: t => pick c joins t

/-- The device this store is in community c as, with its acceptance:
among its acceptances of c whose device's secret it holds, the device
being live, or not admitted with a join still waited on, the admitted
one first, else the least acceptance id. A cut device's entry is not
held (docs/REMOVAL.md, E4), so after a removal the store holds the
community no more and can join it again as a new device. A node holds a
community at most once (libquiet #580, #940); this is which one, and
every reader of the same ops picks the same (the app's switcher, and the
network node). -/
def mine (c : Id) : View Fact (Option (Key × Id)) :=
  .list (accepted.all.query []) fun acc =>
    .list (joining.all.query []) fun joins =>
      (pick c joins.rows acc.rows).bind fun best => .pure (best.map fun (d, a, _) => (d, a))

/-- Whether device d is live in c: admitted, and none of the users it is
admitted into removed. -/
def deviceLive (c : Id) (d : Key) : View Fact Bool := do
  let a ← admission.byDevice.read [c, d]
  if a.rows.isEmpty then pure false else unremoved c a.rows

/-- The acceptance of c this store held until its device was cut (the
first such, with the device's secret held), when `mine` holds none:
not held, so not answered or dialed as, but what a removed member's app
hides and tells its user about. -/
def cutEntry (c : Id) : View Fact (Option (Key × Id)) := do
  let acc ← accepted.all.read []
  for ((_, aid), f) in acc.rows do
    let .accepted c' d := f | continue
    if c' ≠ c then continue
    let sec ← secret.byKey.read [d] (limit := some 0)
    if sec.total = 0 then continue
    let adm ← admission.byDevice.read [c, d] (limit := some 0)
    if adm.total = 0 then continue
    if !(← deviceLive c d) then return some (d, aid)
  return none

/-- Join from a link, to be known as `name`, unless this store already
holds the community (`mine`): then nothing. A join of c stopped waiting
on is resumed rather than made again: a new joining op (one epoch on)
for the same request, so the inviter sees the same request (libquiet's
dormant join); a join whose device was admitted is spent, not dormant.
Otherwise a fresh join (`joinOps`) from this node's key (made from
`fresh` if it has none), unless the seed's device is already admitted
in c: a join never asks for an admitted device, so never for a cut one
(`join_new_device`). -/
def join (i : Invite) (seed name fresh : ByteArray) : View Fact Write :=
  (mine i.community).bind fun held => if held.isSome then .pure ⟨[]⟩ else
  .list (joining.all.query []) fun joins =>
  (dormant i.community joins.rows).bind fun
    | some (k, hs, r, nm, d, n) => .pure ⟨[mkOp [] (.joining i.community k hs r nm d (n + 1))]⟩
    | none =>
      .list (admission.byDevice.query [i.community, (Device.ofSeed seed).pk] (limit := some 0)) fun adm =>
        if adm.total ≠ 0 then .pure ⟨[]⟩ else
        (nodeKeyOr fresh).bind fun (key, pre) => .pure ⟨pre ++ (joinOps i seed name key).ops⟩

/-- Once device d is admitted into c with no profile yet: the first
profile, named as this device's join asked (a node may hold several
joins of c: a raced one, or a rejoin's). Reads my admission, my profile
and my join; writes nothing otherwise. -/
def introduce (c : Id) (d : Device) (time : Nat) : View Fact Write := do
  let adms ← admission.byDevice.read [c, d.pk]
  match adms.rows.head? with
  | some ((_, adm), .admission _ u _ _) =>
    let prof ← profile.byUser.read [c, u] (limit := some 0)
    let joins ← joining.all.read []
    let name := joins.rows.findSome? fun (_, f) => match f with
      | .joining c' _ _ _ nm d' _ => if c' = c ∧ d' = d.pk then some nm else none
      | _ => none
    match name with
    | some nm => pure (if prof.total = 0 then ⟨[profile c adm d nm time]⟩ else ⟨[]⟩)
    | none => pure ⟨[]⟩
  | _ => pure ⟨[]⟩

/-- The first approval of each user, in order. -/
def firstPerUser (l : List (Id × Id)) : List (Id × Id) :=
  l.foldl (fun acc p => if acc.any (fun q => decide (q.2 = p.2)) then acc else acc ++ [p]) []

/-- Approve request req of c as device d (admitted as `myAdm`): my
approval, and the admission too when mine completes the tally. Reads the
request, my admission and the approvals so far. -/
def approveReq (c req myAdm : Id) (d : Device) (esk : ByteArray := .empty) :
    View Fact Write := do
  let ok := approve c req myAdm d
  let rq ← View.read { key := opKey req, limit := some 1 }
  let me ← View.read { key := opKey myAdm, limit := some 1 }
  let aps ← approval.byRequest.read [c, req]
  -- The requester's device gets this device's content key for c,
  -- wrapped to its encryption key: the approval is where key material
  -- hangs (the user's decision, 2026-10-27).
  let ks ← key.byCommunity.read [c] (limit := some 1)
  let wrapTo (e : ByteArray) : List Op := match ks.rows.head? with
    | some (_, .key _ _ k) => if esk.size = 32 then [wrapKey c k esk e] else []
    | _ => []
  match rq.rows.head?, me.rows.head? with
  | some (_, .request _ _ _ e _ t), some (_, .admission _ u _ _) =>
    let others := firstPerUser (aps.rows.filterMap fun (p, f) => match f with
      | .approval _ _ v => if v = u then none else some (p.2, v)
      | _ => none)
    let chosen := ok.id :: others.map (·.1)
    pure (if t ≤ chosen.length then ⟨[ok, admit c req (chosen.take t)] ++ wrapTo e⟩
      else ⟨[ok] ++ wrapTo e⟩)
  | _, _ => pure ⟨[ok]⟩

/-- The ids of the content keys of c this device holds. -/
def heldKids (c : Id) : View Fact (List ByteArray) := do
  let ks ← key.byCommunity.read [c] (limit := none)
  pure (ks.rows.filterMap fun (_, f) => match f with | .key _ kid _ => some kid | _ => none)

/-- The messages of c this device can read, in the channel's order: the
union of the lists of messages under each content key it holds
(`message.byKey [c, kid]`, by counter, time and id), then of its receipts
of saturated ones (`received.byKey [c, kid]`, in the order it received
them), each row named by its message (`asMsg`). A message sealed under a
key not yet held is not listed. When the key arrives,
`key.byCommunity [c]` is filed, so a live reader of this view reads
again and the message appears. Ranges and limits are a list's (`after`,
`before`, `limit`, `desc`), so pages and counts are the union's; a bound
is a row's position (a receipt's sort key names its message, so a
receipt list is bounded by sort key alone). -/
def readable (c : Id) (limit : Option Nat := some 50) (desc : Bool := true)
    (after before : Option Pos := none) : View Fact (Answer Fact) := do
  let kids ← heldKids c
  let ms ← View.readAll (kids.map fun kid => message.byKey.query [c, kid] limit desc after before)
  let rs ← View.readAll (kids.map fun kid =>
    received.byKey.query [c, kid] limit desc (after.map afterRec) (before.map beforeRec))
  pure (unionAnswers desc limit (ms ++ rs.map fun a => { a with rows := a.rows.map asMsg }))

/-- A clump list uses exactly the same query API and pagination as the
message timeline. `none` lists roots; `some root` lists that root's children.
Saturated messages still use this device's receipts, including in clumps. -/
def readableClumps (c : Id) (root : Option Id) (limit : Option Nat := some 50)
    (desc : Bool := true) (after before : Option Pos := none) : View Fact (Answer Fact) := do
  let kids ← heldKids c
  let (messages, receipts, args) := match root with
    | none => (message.rootsByKey, received.rootsByKey, [c])
    | some r => (message.childrenByKey, received.childrenByKey, [c, r])
  let ms ← View.readAll (kids.map fun kid => messages.query (args ++ [kid]) limit desc after before)
  let rs ← View.readAll (kids.map fun kid =>
    receipts.query (args ++ [kid]) limit desc (after.map afterRec) (before.map beforeRec))
  return unionAnswers desc limit (ms ++ rs.map fun a => { a with rows := a.rows.map asMsg })

/-- This device's newest content key for c, if it holds one. -/
def currentKey (c : Id) : View Fact (Option ByteArray) := do
  let ks ← key.byCommunity.read [c] (limit := some 1)
  pure (ks.rows.head?.bind fun (_, f) => match f with | .key _ _ k => some k | _ => none)

/-- The content keys of c wrapped to this node's key that it does not
hold yet, opened with the key's secret: each becomes a local `key`. -/
def unwrap (c : Id) : View Fact Write := do
  let some (pk, sk) ← nodeKey | pure ⟨[]⟩
  let ws ← wrap.byRecipient.read [c, pk]
  let mut out : List Op := []
  for (_, f) in ws.rows do
    let .wrap _ kid _ bx := f | continue
    let held ← key.byId.read [kid] (limit := some 0)
    if held.total ≠ 0 then continue
    match unbox cryptoSeal sk kid bx with
    | some k => if k.size = 32 && !out.any (fun o => o.body == (contentKey c k).body) then
        out := out ++ [contentKey c k]
    | none => pure ()
  pure ⟨out⟩

/-- Remove user t from c (libquiet's remover flow), as this device's
user u: the removal cites the root, this device's admission, what makes
u an admin (its own admission for the founder, else a grant), and an
admission of t. Nothing when u is not an admin, t is u, or t is already
removed (`removeMember_valid`). -/
def removeMember (c t : Id) (d : Device) : View Fact Write := do
  let me ← admission.byDevice.read [c, d.pk] (limit := some 1)
  let gone ← removal.byUser.read [c, t] (limit := some 0)
  let tgt ← admission.byUser.read [c, t] (limit := some 1)
  match me.rows.head? with
  | some ((_, myAdm), .admission _ u _ _) =>
    let grant ← admin.byUser.read [c, u] (limit := some 1)
    let auth := if u = c then some myAdm else grant.rows.head?.map (·.1.2)
    match auth, tgt.rows.head? with
    | some a, some ((_, ta), _) =>
      pure ⟨if u = t ∨ gone.total ≠ 0 then [] else [remove c myAdm a ta d]⟩
    | _, _ => pure ⟨[]⟩
  | _ => pure ⟨[]⟩
end Community
namespace Community
open Engine Codec

@[extern "le_ed25519_verify"] opaque edVerify (pk msg sig : @& ByteArray) : Bool

def ed25519 : Crypto := ⟨fun pk m s => edVerify pk m s, fun seed => (edKeypair seed).extract 0 32⟩

def Device.named (name : String) : Device := Device.ofSeed (sha256 name.toUTF8)

/-- An attachment's info and the file's key and nonce, opened with the
content key. -/
def openInfo (c kid sealed k : ByteArray) : Option (FileMeta × ByteArray × ByteArray) :=
  (openSealed cryptoSeal c kid sealed k).bind fun m =>
    (decode m : Option (ByteArray × ByteArray × Nat × Nat × ByteArray × ByteArray × ByteArray)).map
      fun (n, kd, w, h, p, fk, fn) => (⟨n, kd, w, h, p⟩, fk, fn)

/-- A file from its chunks' slices, in order, opened with its key. -/
def openFile (slices : List ByteArray) (fileKey fileNonce : ByteArray) : Option ByteArray :=
  cryptoSeal.dec fileKey fileNonce fileAd (Merkle.assemble slices)
end Community
namespace Community
open Engine

/-- The admissions into c among these rows whose device is live: each
one's user, device and key. -/
def live (c : Id) : List (Pos × Fact) → View Fact (List (Id × Key × Key))
  | [] => .pure []
  | (_, .admission c' u d e) :: t =>
    if c' = c then
      (deviceLive c d).bind fun ok =>
        (live c t).bind fun rest => .pure (if ok then (u, d, e) :: rest else rest)
    else live c t
  | _ :: t => live c t

/-- Whether to sync community c with the node whose key is e: the
admissions under e, and whether each one's device is live. -/
def allowPeer (c : Id) (e : Key) : View Fact Bool := do
  let a ← admission.byKey.read [c, e]
  let ls ← live c a.rows
  pure (ls.any fun l => decide (l.2.2 = e))

/-- The device keys of c's live devices. -/
def members (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map (·.2.1))

/-- The node keys a new content key of c is wrapped to: those with a
live device, the keys `allowPeer` lets in. -/
def recipients (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map (·.2.2))

/-- Of these rows, each admission's user's removals in c, as op ids. -/
def removalsOf (c : Id) : List (Pos × Fact) → View Fact (List Id)
  | [] => .pure []
  | (_, .admission _ u _ _) :: t =>
    .list (removal.byUser.query [c, u]) fun a =>
      (removalsOf c t).bind fun rest => .pure (a.rows.map (·.1.2) ++ rest)
  | _ :: t => removalsOf c t

/-- Of these admission rows, the removals of every user each row's
device is admitted into, under any key. -/
def deviceRemovals (c : Id) : List (Pos × Fact) → View Fact (List Id)
  | [] => .pure []
  | (_, .admission _ _ d _) :: t =>
    .list (admission.byDevice.query [c, d]) fun a =>
      (removalsOf c a.rows).bind fun xs =>
        (deviceRemovals c t).bind fun rest => .pure (xs ++ rest)
  | _ :: t => deviceRemovals c t

/-- The removals that cut the devices admitted under key e in c: every
removal of a user any of those devices is admitted into. What a node
holding them owes the node at e once none of its devices is live, so
that node can judge itself cut (docs/REMOVAL.md). -/
def removalsAt (c e : Key) : View Fact (List Id) := do
  let a ← admission.byKey.read [c, e]
  deviceRemovals c a.rows

end Community

namespace Connection
open Engine Codec Community

/-- Whether op o is a join request of community c: the one thing a
hello delivers. -/
def joinOf (c : B) (o : Op) : Bool :=
  decide (o.reqs.head? = some c) &&
    decide (o.kind = Community.Body.tag (.request .empty .empty .empty .empty)) &&
    match (decode o.body : Option Community.Body) with
    | some (.request ..) => true
    | _ => false

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

end Connection
