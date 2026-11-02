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
import app.community.notice.Commands
import app.community.caughtUp.Commands
import app.community.profile.Commands

namespace Community
open Engine Codec

/-- The root of a community founded by device d on the node with key
`key`, its content key's id `kid`: the founder's admission names all
three, signed by d. -/
def root (d : Device) (key : Key) (kid : ByteArray) : Op :=
  mkOp [] (.root d.pk key kid (sig d.sk [] (.root d.pk key kid .empty)))
open Engine

/-- Found a community named `name` from this device's seed, the founder
known as `myName`: this node's key if it has none (from `fresh`), the
device's secret (local), the root (naming the device, the node's key
and the id of the community's content key `k`), the device's acceptance
(local), the first name, the founder's first profile (the root is the
founder's admission), and `k` itself (local), wrapped by the device to
its own node's key with ephemeral secret `esk` (fresh random bytes from
the caller, as `fresh` and `k` are). -/
def found (seed name myName : ByteArray) (time : Nat) (k esk fresh : Key32) :
    View Fact Write := do
  let (key, pre) ← nodeKeyOr fresh
  let d := Device.ofSeed seed
  let r := root d key (kidOf cryptoSeal k)
  pure ⟨pre ++ [secret seed, r, accept r.id d.pk, setName r.id r.id r.id [] 1 d name,
    profile r.id r.id d myName time, contentKey r.id k.1, wrapKey r.id r.id r.id d k esk key]⟩

/-- Invite to c from device d (admitted as `myAdm`): the invitation,
and its link, naming this node's key, with the bearer seed and dial
hints given. None on a node with no key (a node that founded or joined
nothing). -/
def inviteTo (c myAdm : Id) (d : Device) (bearerSeed : ByteArray) (hints : List ByteArray) (link : Bool := false) :
    View Fact (Option (Write × Invite)) := do
  let some (key, _) ← nodeKey | pure none
  let p := issue c myAdm d key bearerSeed hints link
  pure (some (⟨[p.1]⟩, p.2))

/-- Join from a link, from the node with key `key`, to be known as
`name`: the device's secret, its request (the one op that travels), its
acceptance of the community, and the pending join (which keeps the name
until admission). -/
def joinOps (i : Invite) (seed name : ByteArray) (key : Key) : Write :=
  let d := Device.ofSeed seed
  let req := i.request d key
  -- a device link joins its issuer's user, whose profile it syncs: no name
  ⟨[secret seed, req, accept i.community d.pk, joining i req.id (if i.link then .empty else name) d.pk]⟩

/-! ## The causal cut, read (`Behind`, `Kept`, `Counts`, `Trusted`)

Every list these read is a relation's, so the trust rule answers on the
node's composed store as on its Community part (`reads_allowPeer`). An
approval's fact is found by its id among a list's rows: its device's
chain (`approval.byDev`) or its approver's admitting approvals
(`approval.byRequester`). -/

/-- Approval x's fact among these rows, if one is x's. -/
def factIn (x : Id) : List (Pos × Fact) → Option Approve.Fact
  | [] => none
  | ((_, y), .ofApproval f) :: t => if y = x then some f else factIn x t
  | _ :: t => factIn x t

/-- Whether approval x is h, k previous links back from h, through these
rows (h's device's chain). -/
def behindIn (rows : List (Pos × Fact)) (x : Id) : Nat → Id → Bool
  | 0, h => decide (h = x)
  | k + 1, h => match factIn h rows with
    | some f => f.n != 0 && behindIn rows x k f.prev
    | none => false

/-- Whether approval x (fact f) is inside cut k: behind a head k names for
its device, its device's chain being these rows. -/
def inCut (rows : List (Pos × Fact)) (x : Id) (f : Approve.Fact) : List (Key × Id × Nat) → Bool
  | [] => false
  | (d, h, m) :: t => (decide (d = f.dev ∧ f.n ≤ m) && behindIn rows x (m - f.n) h) || inCut rows x f t

/-- Whether every removal among these rows keeps approval x (fact f),
its device's chain being `chain`. -/
def cutsKeep (chain : List (Pos × Fact)) (x : Id) (f : Approve.Fact) : List (Pos × Fact) → Bool
  | [] => true
  | (_, .ofRemoval r) :: t => inCut chain x f r.cut && cutsKeep chain x f t
  | _ :: t => cutsKeep chain x f t

/-- Whether every removal of every user of c among these admission rows
keeps approval x (fact f). Its device's chain is read only for a user
with a removal. -/
def usersKeep (c x : Id) (f : Approve.Fact) : List (Pos × Fact) → View Fact Bool
  | [] => .pure true
  | (_, .admission c' u _ _ _) :: t =>
    if c' = c then
      .list (removal.byUser.query [c, u]) fun a =>
        if a.rows.isEmpty then usersKeep c x f t
        else .list (approval.byDev.query [c, f.dev]) fun ch =>
          if cutsKeep ch.rows x f a.rows then usersKeep c x f t else .pure false
    else usersKeep c x f t
  | _ :: t => usersKeep c x f t

/-- Whether approval x (fact f) is kept: every removal of every user its
device is admitted into keeps it (`kept_iff`). -/
def kept (c x : Id) (f : Approve.Fact) : View Fact Bool :=
  .list (admission.byDevice.query [c, f.dev]) fun a => usersKeep c x f a.rows

/-- Whether approval x (fact f) counts in c, following `up` at most k
times: kept, and the founder's device's, or its `up` counts. Read with
k = its depth + 1, which reaches the founder's (`counts_iff`). -/
def counts (c : Id) : Nat → Id → Approve.Fact → View Fact Bool
  | 0, _, _ => .pure false
  | k + 1, x, f => (kept c x f).bind fun ok =>
    if !ok then .pure false
    else if f.depth = 0 then .pure true
    else .list (approval.byRequester.query [c, f.dev]) fun a =>
      match factIn f.up a.rows with
      | some g => counts c k f.up g
      | none => .pure false

/-- Whether an approval among these rows approves a request for an
admission into user u with key e, and counts. -/
def approvedBy (c u : Id) (e : Key) : List (Pos × Fact) → View Fact Bool
  | [] => .pure false
  | ((_, x), .ofApproval f) :: t =>
    if f.ru = u ∧ f.re = e then
      (counts c (f.depth + 1) x f).bind fun b => if b then .pure true else approvedBy c u e t
    else approvedBy c u e t
  | _ :: t => approvedBy c u e t

/-- Whether fact g is an admission into user u of c of device d with key
e, under any key id (the root's: `root_of_admission`). -/
def isAdmission (c u : Id) (d e : Key) : Fact → Bool
  | .admission c' u' d' e' _ => decide (c' = c ∧ u' = u ∧ d' = d ∧ e' = e)
  | _ => false

/-- Whether admission (c, u, d, e) is trusted: the root's, or an approval
of a request for it counts (`trusted_iff`). -/
def trusted (c u : Id) (d e : Key) : View Fact Bool :=
  .list (admission.byDevice.query [c, d]) fun r =>
    if r.rows.any (fun ((_, y), g) => decide (y = c) && isAdmission c u d e g) then .pure true
    else .list (approval.byRequester.query [c, d]) fun a => approvedBy c u e a.rows

/-- Whether every admission into c among these rows is into a user with
no removal. -/
def unremoved (c : Id) : List (Pos × Fact) → View Fact Bool
  | [] => .pure true
  | (_, .admission c' u _ _ _) :: t =>
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

/-- Whether device d is cut from c: admitted, and one of the users it is
admitted into removed. Only a removal read makes it so: a read that
finds no admission (not yet written, or not yet seen) says not cut, so a
member is never told of a removal no one made (`deviceCut_removal`). -/
def deviceCut (c : Id) (d : Key) : View Fact Bool := do
  let a ← admission.byDevice.read [c, d]
  if a.rows.isEmpty then pure false else return !(← unremoved c a.rows)

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
    if ← deviceCut c d then return some (d, aid)
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
def join (i : Invite) (seed name : ByteArray) (fresh : Key32) : View Fact Write :=
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
joins of c: a raced one, or a rejoin's). A join with no name (a device
link's, `joinOps`) writes none: its user has a profile, which may not
have synced yet. Reads my admission, my profile and my join; writes
nothing otherwise. -/
def introduce (c : Id) (d : Device) (time : Nat) : View Fact Write := do
  let adms ← admission.byDevice.read [c, d.pk]
  match adms.rows.head? with
  | some ((_, adm), .admission _ u _ _ _) =>
    let prof ← profile.byUser.read [c, u] (limit := some 0)
    let joins ← joining.all.read []
    let name := joins.rows.findSome? fun (_, f) => match f with
      | .joining c' _ _ _ nm d' _ => if c' = c ∧ d' = d.pk then some nm else none
      | _ => none
    match name with
    | some nm => pure (if prof.total = 0 ∧ nm.isEmpty = false then ⟨[profile c adm d nm time]⟩ else ⟨[]⟩)
    | none => pure ⟨[]⟩
  | _ => pure ⟨[]⟩

/-- c's content key id, as its root names it; none until the root is
Valid here. -/
def communityKid (c : Id) : View Fact (Option ByteArray) := do
  let a ← View.read { key := opKey c, limit := some 1 }
  pure (match a.rows.head? with
    | some (_, .admission c' _ _ _ kid) => if c' = c then some kid else none
    | _ => none)

/-- c's content key, if this device holds it: the key filed under the id
c's root names (`key_kid`: a key is filed under its own hash). Keys do
not rotate yet, so it is the one key every post of c is sealed under. -/
def currentKey (c : Id) : View Fact (Option Key32) := do
  let some kid ← communityKid c | pure none
  let ks ← key.byId.read [kid] (limit := some 1)
  pure (ks.rows.head?.bind fun (_, f) => match f with | .key _ _ k => Bytes.of? k | _ => none)

/-- Of these rows (approvals of my requests), the first approving
admission (u, e) that counts, else the first approving it. -/
def upIn (c u : Id) (e : Key) : List (Pos × Fact) → View Fact (Option Id)
  | [] => .pure none
  | ((_, x), .ofApproval f) :: t =>
    if f.ru = u ∧ f.re = e then
      (counts c (f.depth + 1) x f).bind fun b =>
        if b then .pure (some x) else (upIn c u e t).bind fun r => .pure (r.orElse fun _ => some x)
    else upIn c u e t
  | _ :: t => upIn c u e t

/-- The approval to cite as the one that admitted me, a device whose
admission is `me` (none when `me` is the root's own, the founder's
device): of the approvals of my requests for that admission, the first
that counts, else the first (`upIn`). -/
def upFor (c : Id) (me root : Fact) : View Fact (Option Id) :=
  match me with
  | .admission _ u d e _ =>
    if me = root then .pure none
    else .list (approval.byRequester.query [c, d]) fun a => upIn c u e a.rows
  | _ => .pure none

/-- `upFor`, from the reads of my admission and of the root. -/
def upOf (c : Id) (me root : Answer Fact) : View Fact (Option Id) :=
  match me.rows.head?, root.rows.head? with
  | some (_, m), some (_, r) => upFor c m r
  | _, _ => .pure none

/-- Approve request req of c as device d (admitted as `myAdm`): my
approval and the admission it gives (one approval admits), with the
community's key wrapped by d to the requester's node, citing that
admission; only the approval if it does not hold the request or my
admission. The approval cites the approval that admitted me (`upFor`)
and my newest approval (the head of my chain, `approval.byDev`), so my
approvals form one chain. Reads the request, my admission, the root, my
approvals and c's key. -/
def approveReq (c req myAdm : Id) (d : Device) (esk : ByteArray := .empty) :
    View Fact Write := do
  let rq ← View.read { key := opKey req, limit := some 1 }
  let me ← View.read { key := opKey myAdm, limit := some 1 }
  let rt ← View.read { key := opKey c, limit := some 1 }
  let up ← upOf c me rt
  let head ← approval.byDev.read [c, d.pk] (limit := some 1)
  -- The requester's device gets the community's key, wrapped to its
  -- encryption key: the approval is where key material hangs (the
  -- user's decision, 2026-10-27).
  let k? ← currentKey c
  let ok := approve c req myAdm d up (head.rows.head?.map (·.1.2))
  match rq.rows.head?, me.rows.head? with
  | some (_, .request _ _ _ e _), some (_, .admission ..) =>
    let adm := admit c req ok.id
    pure ⟨[ok, adm] ++ (match k?, Bytes.of? esk with
      | some k, some esk => [wrapKey c myAdm adm.id d k esk e]
      | _, _ => [])⟩
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

/-- c's content key, from the wraps to this node's key, once c's root is
Valid here and this device does not hold the key yet: the first wrap
that opens with the node's secret to a key whose id is the root's
becomes a local `key`. A wrap holding any other key (a member's plant)
is passed over (`unwrap_community`). -/
def unwrap (c : Id) : View Fact Write := do
  let some (pk, sk) ← nodeKey | pure ⟨[]⟩
  let some kid ← communityKid c | pure ⟨[]⟩
  let held ← key.byId.read [kid] (limit := some 0)
  if held.total ≠ 0 then return ⟨[]⟩
  let ws ← wrap.byRecipient.read [c, pk]
  let ks := ws.rows.filterMap fun (_, f) => match f with
    | .wrap _ _ _ bx => (unbox cryptoSeal sk kid bx).filter fun k => decide (kidOf cryptoSeal k = kid)
    | _ => none
  pure ⟨(ks.head?.map fun k => contentKey c k.1).toList⟩

/-- The most heads a removal cites: the intake caps an op at 64
requirements, and a removal's first four are fixed. -/
def maxHeads : Nat := 60

/-- The heads of the approval chains of these admissions' devices, each
device once (`seen`): its newest approval, the last of its chain
(`approval.byDev`, by place). -/
def headsOf (c : Id) : List Key → List (Pos × Fact) → View Fact (List Id)
  | _, [] => .pure []
  | seen, (_, .admission _ _ d _ _) :: t =>
    if seen.any (fun k => decide (k = d)) then headsOf c seen t
    else .list (approval.byDev.query [c, d] (limit := some 1)) fun a =>
      (headsOf c (d :: seen) t).bind fun rest =>
        .pure (match a.rows.head? with | some ((_, h), _) => h :: rest | none => rest)
  | seen, _ :: t => headsOf c seen t

/-! ## Notifications: a user's private state, in notice ops -/

/-- A user's notification state as this device opens it. -/
structure NoticeState where
  read : List Id := []
  settings : Notice.Settings := {}
  /-- The revision the settings were set at. -/
  settingsRev : Nat := 0
  /-- The newest notice's revision. -/
  revision : Nat := 0
  deriving Inhabited

/-- How many of the newest notices sealed to this device are read. -/
def noticeWindow : Nat := 64

/-- A box of a 32-byte key: the ephemeral public key, the key, its tag. -/
def noticeBoxSize : Nat := 80

/-- A notice's payload sealed to the device whose X25519 key is `rpk`:
a one-time 32-byte key `nk` wrapped to it (`box`, bound to the community
and the user), then the payload under `nk` (`sealBody`, its associated
data the community and the user). One key, one message: the nonce is
zero. -/
def sealNotice (esk nk : Key32) (rpk c u payload : ByteArray) : ByteArray :=
  box cryptoSeal esk rpk (Notice.binding c u) nk ++ sealBody cryptoSeal nk zeros24 c u payload

/-- Notice payload bx of user u of c, opened with this node's secret. -/
def openNotice (sk : Key32) (c u bx : ByteArray) : Option Notice.Payload := do
  let nk ← unbox cryptoSeal sk (Notice.binding c u) (bx.extract 0 noticeBoxSize)
  let bytes ← openBody cryptoSeal nk zeros24 c u (bx.extract noticeBoxSize bx.size)
  Codec.decode bytes

/-- User u's state from notice rows (newest first): every read they
name; the settings of the highest settings revision. Rows by another
user, or that do not open, count for nothing. -/
def noticeOf (sk : Key32) (c u : Id) (rows : List (Pos × Fact)) : NoticeState := Id.run do
  let mut out : NoticeState := {}
  for (_, f) in rows do
    let .notice _ author _ bx rev := f | continue
    if author != u then continue
    let some (reads, cl, ch, srev) := openNotice sk c u bx | continue
    out := { out with read := out.read ++ reads, revision := max out.revision rev }
    if srev > out.settingsRev then
      let settings : Notice.Settings := { community := Notice.Level.ofCode cl, conversation := Notice.Level.ofCode ch }
      out := { out with settingsRev := srev, settings }
  return out

/-- User u's notification state in c: the newest `noticeWindow` notices
sealed to this node. A bounded read, however many notices there are. -/
def noticeState (c u : Id) : View Fact NoticeState := do
  let some (pk, sk) ← nodeKey | pure {}
  let a ← notice.byRecipient.read [c, pk] (limit := some noticeWindow)
  pure (noticeOf sk c u a.rows)

/-- The devices a notice is sealed to: the node keys of the admissions
among `rows` (the user's own: `admission.byUser [c, u]`), each once;
for reads (`all` false), not this node's own key. -/
def noticeRecipients (pk : Key) (all : Bool) : List (Pos × Fact) → List Key
  | [] => []
  | (_, .admission _ _ _ enc _) :: rest =>
    let r := noticeRecipients pk all rest
    if Engine.has r enc || (!all && decide (enc = pk)) then r else enc :: r
  | _ :: rest => noticeRecipients pk all rest

/-- What records user u's new reads, or settings, in c: one notice per
device admitted into u (`noticeRecipients_own`), sealed to that device's
key: reads only to the other devices (this one keeps its own), settings
to every device, this one included. Notices are local today
(`notice_local`): with device linking they travel only between the
user's own devices. Each box's ephemeral secret is derived from `fresh`
and its recipient. Every notice carries the settings, at their revision. -/
def noticeWrite (c adm u : Id) (d : Device) (fresh : ByteArray) (reads : List Id)
    (settings : Option Notice.Settings := none) : View Fact Write := do
  let some (pk, _) ← nodeKey | pure ⟨[]⟩
  let old ← noticeState c u
  let (s, srev) := match settings with
    | some s => (s, old.settingsRev + 1)
    | none => (old.settings, old.settingsRev)
  let payload : Notice.Payload := (reads, Notice.Level.code s.community, Notice.Level.code s.conversation, srev)
  let ads ← admission.byUser.read [c, u] (limit := none)
  pure ⟨(noticeRecipients pk settings.isSome ads.rows).filterMap fun enc => do
    -- the ephemeral secret and the one-time key, from `fresh` and the
    -- recipient (32-byte hashes)
    let esk ← Bytes.of? (cryptoSeal.hash ("quiet/notify/esk".toUTF8 ++ fresh ++ enc))
    let nk ← Bytes.of? (cryptoSeal.hash ("quiet/notify/key".toUTF8 ++ fresh ++ enc))
    pure (notice c adm d enc (sealNotice esk nk enc c u (Codec.encode payload)) (old.revision + 1))⟩

/-! ## Message links: a message's destination (libquiet's `quiet://open/…`) -/

/-- Where a link opens: a community, a conversation in it, and a message
there; a thread reply names its root first. Ids, never names. -/
structure Target where
  community : Id
  conversation : Id
  message : Id
  root : List Id := []
  deriving BEq, Inhabited

/-- Sizes: 32-byte ids; at most one root. -/
def Target.Valid (t : Target) : Prop :=
  t.community.size = 32 ∧ t.conversation.size = 32 ∧ t.message.size = 32 ∧
    t.root.length ≤ 1 ∧ ∀ r ∈ t.root, r.size = 32

instance (t : Target) : Decidable t.Valid := by unfold Target.Valid; infer_instance

/-- The app's scheme for a message, beside the invites' `leanquiet://join/`
and device links' `leanquiet://link/`. -/
def openScheme : List Char := "leanquiet://open/".toList

/-- The kind a message link's fields lead with, after the member link's
1 and the device link's 2 (`kindOf`): no link of one kind reads as
another. -/
def messageKind : Nat := 3

/-- The fields' bytes, behind their kind, in base62. -/
def Target.code (t : Target) : List Char :=
  Base62.encode (encode (messageKind, t.community, t.conversation, t.message, t.root)).data.toList

def Target.uri (t : Target) : String := String.ofList (openScheme ++ t.code)

/-- A message link from text: only this scheme, then the fields. -/
def Target.parse (s : String) : Option Target :=
  let cs := s.toList
  if !openScheme.isPrefixOf cs then none else
  match Base62.decode (cs.drop openScheme.length) with
  | none => none
  | some bs =>
    match (Codec.decode ⟨bs.toArray⟩ : Option (Nat × Id × Id × Id × List Id)) with
    | some (v, c, ch, m, r) =>
      let t : Target := ⟨c, ch, m, r⟩
      if v = messageKind ∧ t.Valid then some t else none
    | none => none

/-- Remove user t from c (libquiet's remover flow), as this device's
user u: the removal cites the root, this device's admission, what makes
u an admin (its own admission for the founder, else a grant), an
admission of t, and the head of each of t's devices' approval chains
this store holds: its cut, so t's approvals seen here keep admitting
(`removeMember_keeps`). Nothing when u is not an admin, t is u, or t is
already removed (`removeMember_valid`). -/
def removeMember (c t : Id) (d : Device) : View Fact Write := do
  let me ← admission.byDevice.read [c, d.pk] (limit := some 1)
  let gone ← removal.byUser.read [c, t] (limit := some 0)
  let tgt ← admission.byUser.read [c, t]
  match me.rows.head? with
  | some ((_, myAdm), .admission _ u _ _ _) =>
    let grant ← admin.byUser.read [c, u] (limit := some 1)
    let auth := if u = c then some myAdm else grant.rows.head?.map (·.1.2)
    match auth, tgt.rows.head? with
    | some a, some ((_, ta), _) =>
      let hs ← headsOf c [] tgt.rows
      pure ⟨if u = t ∨ gone.total ≠ 0 then [] else [remove c myAdm a ta d (hs.take maxHeads)]⟩
    | _, _ => pure ⟨[]⟩
  | _ => pure ⟨[]⟩
open Engine Codec

def ed25519 : Crypto := ⟨fun pk m s => edVerify pk m s, fun seed => (edKeypair seed).extract 0 32⟩

def Device.named (name : String) : Device := Device.ofSeed (sha256 name.toUTF8)

/-- **A device made from a 32-byte seed verifies its own signatures**,
under the crypto trust file's Ed25519 clause: the premise the signing
laws take (`hsig`, `Scene.Good.ofSigning`), for every device the app
makes from a seed. -/
theorem ofSeed_signs (t : Trust.Ed25519Signs) (seed : Key32) (m : ByteArray) :
    ed25519.verify (Device.ofSeed seed.1).pk m (edSign (Device.ofSeed seed.1).sk m) = true :=
  t seed m

/-- **A named device verifies its own signatures**: its seed is a SHA-256
digest, 32 bytes (`Trust.Sha256Size`). -/
theorem named_signs (hs : Trust.Sha256Size) (t : Trust.Ed25519Signs) (name : String) (m : ByteArray) :
    ed25519.verify (Device.named name).pk m (edSign (Device.named name).sk m) = true :=
  ofSeed_signs t ⟨sha256 name.toUTF8, hs _⟩ m

/-- An attachment's info and the file's key and nonce, opened with the
content key. -/
def openInfo (c kid sealed k : ByteArray) : Option (FileMeta × ByteArray × ByteArray) :=
  (openStored cryptoSeal c kid sealed k).bind fun m =>
    (decode m : Option (ByteArray × ByteArray × Nat × Nat × ByteArray × ByteArray × ByteArray)).map
      fun (n, kd, w, h, p, fk, fn) => (⟨n, kd, w, h, p⟩, fk, fn)

/-- A file from its chunks' slices, in order, opened with its key. -/
def openFile (slices : List ByteArray) (fileKey fileNonce : ByteArray) : Option ByteArray :=
  match Bytes.of? fileKey, Bytes.of? fileNonce with
  | some k, some n => cryptoSeal.dec k n fileAd (Merkle.assemble slices)
  | _, _ => none
open Engine

/-- The admissions into c among these rows whose device is live: each
one's user, device and key. The people list reads it. -/
def live (c : Id) : List (Pos × Fact) → View Fact (List (Id × Key × Key))
  | [] => .pure []
  | (_, .admission c' u d e _) :: t =>
    if c' = c then
      (deviceLive c d).bind fun ok =>
        (live c t).bind fun rest => .pure (if ok then (u, d, e) :: rest else rest)
    else live c t
  | _ :: t => live c t

/-- The admissions into c among these rows the trust rule lets in: each
trusted (`trusted`) and its device live. Each one's user, device and
key. -/
def letIn (c : Id) : List (Pos × Fact) → View Fact (List (Id × Key × Key))
  | [] => .pure []
  | (_, .admission c' u d e _) :: t =>
    if c' = c then
      (trusted c u d e).bind fun tr => (deviceLive c d).bind fun ok =>
        (letIn c t).bind fun rest => .pure (if tr && ok then (u, d, e) :: rest else rest)
    else letIn c t
  | _ :: t => letIn c t

/-- Whether to sync community c with the node whose key is e: the
admissions under e, whether each is trusted, and whether its device is
live. -/
def allowPeer (c : Id) (e : Key) : View Fact Bool := do
  let a ← admission.byKey.read [c, e]
  let ls ← letIn c a.rows
  pure (ls.any fun l => decide (l.2.2 = e))

/-- The device keys of c's live devices with a trusted admission. -/
def members (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← letIn c a.rows
  pure (ls.map (·.2.1))

/-- The node keys a new content key of c is wrapped to: those with a
trusted admission of a live device, the keys `allowPeer` lets in. -/
def recipients (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← letIn c a.rows
  pure (ls.map (·.2.2))

/-- Of these rows, each admission's user's removals in c, as op ids. -/
def removalsOf (c : Id) : List (Pos × Fact) → View Fact (List Id)
  | [] => .pure []
  | (_, .admission _ u _ _ _) :: t =>
    .list (removal.byUser.query [c, u]) fun a =>
      (removalsOf c t).bind fun rest => .pure (a.rows.map (·.1.2) ++ rest)
  | _ :: t => removalsOf c t

/-- Of these admission rows, the removals of every user each row's
device is admitted into, under any key. -/
def deviceRemovals (c : Id) : List (Pos × Fact) → View Fact (List Id)
  | [] => .pure []
  | (_, .admission _ _ d _ _) :: t =>
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
