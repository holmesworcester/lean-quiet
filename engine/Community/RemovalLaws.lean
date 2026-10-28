/-
The Community side of docs/REMOVAL.md, stated of the views and intents
that run, at rest (queue empty) over the persisted tables. Statements
(`_stmt`), proven in phase 2.

E3, a node's key:
- `connect_iff_stmt`, `refuse_nonmember_stmt`, `removal_cuts_off_stmt`,
  `connect_admitted_stmt`: `allowPeer c e` asks about a node's key e (an
  admission's X25519 key, which the node's handshake runs on), and lets
  it in exactly when a device admitted under e is in a live user. These
  replace `connect_iff`, `refuse_nonmember`, `removal_cuts_off` and
  `connect_admitted` (which asked about device keys); `connect_agree`
  and `recipients_iff` stand as they are.
- `new_device_trusted_stmt`: so a removed user's device does not block
  a new device on the same node: one live admission under e is enough.
- `endpoint_signed_stmt`: the binding. An admission's key was signed by
  its device: the root or request it came from carries both, signed by
  the device. (True of the code today; it becomes the binding once e
  is the node's key.)
- `endpoint_derives_stmt`: a Valid endpoint fact's key is its secret's.
- `removals_at_stmt`: `removalsAt c e` lists exactly the removals of
  users admitted under e: the notices owed to the node at e.

E4, a removed entry is not held:
- `mine_not_removed_stmt`: `mine c` never names a device whose every
  admission in c is into a removed user.
- `rejoin_fresh_stmt`: after removal, `join` writes a fresh join for
  the new device's seed (phase 2: plus the node key, `fresh`).
- `join_new_device_stmt`: a join never asks for a device already
  admitted in the community, so never for a removed one.
- `removed_stays_removed_stmt`: whatever is written after, u stays
  removed, and no key is let in for u.
-/
import Community.Intents

namespace Community
open Engine

/-! ## E3: a node's key -/

/-- **Who we connect to, by node key (`connect_iff`).** At rest,
`allowPeer c e` accepts key e exactly when some device admitted under e
is in a user of c not removed. -/
def connect_iff_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key), Inv (family C) s → s.queue = [] →
    ((allowPeer c e).eval s = true ↔ ∃ u d, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u)

/-- **No connection to a node with no live member (`refuse_nonmember`).** -/
def refuse_nonmember_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key), Inv (family C) s → s.queue = [] →
    (∀ u d, Admitted C s.ops c u d e → Removed C s.ops c u) → (allowPeer c e).eval s = false

/-- **A removal cuts off the removed user's node (`removal_cuts_off`)**,
unless a device of another, live user is admitted under its key. -/
def removal_cuts_off_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c u : Id) (e : Key), Inv (family C) s → s.queue = [] →
    Removed C s.ops c u → (∀ u' d, Admitted C s.ops c u' d e → u' = u) →
    (allowPeer c e).eval s = false

/-- **An approved device's node is let in (`connect_admitted`).** A
request tallied by an admit op with its threshold of approvals by
distinct users lets in the key the request names, unless its user has
been removed. -/
def connect_admitted_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (y c r : Id) (o : Op) (aps us : List Id) (d0 e0 : Key) (u : Id)
    (d e : Key) (l : Bool) (t : Nat),
    Inv (family C) s → s.queue = [] →
    s.ops y = some o → (Codec.decode o.body : Option Body) = some .admit →
    o.kind = Body.tag .admit → o.reqs = c :: r :: aps → V C s.ops c (.admission c c d0 e0) →
    V C s.ops r (.request c u d e l t) →
    All2 (fun a v => V C s.ops a (.approval c r v)) aps us → us.Nodup → us.length = t →
    ¬ Removed C s.ops c u → (allowPeer c e).eval s = true

/-- **A new device on a removed user's node is let in
(`new_device_trusted`).** A node whose key names a removed user's device
is let in once a device of a live user is admitted under the same key:
the removed device does not block the node. -/
def new_device_trusted_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c u u2 : Id) (d d2 e : Key), Inv (family C) s → s.queue = [] →
    Admitted C s.ops c u d e → Removed C s.ops c u →
    Admitted C s.ops c u2 d2 e → ¬ Removed C s.ops c u2 → (allowPeer c e).eval s = true

/-- **The binding (`endpoint_signed`).** Every admission's key was
signed by its device: the admission came from a root or a request whose
body carries the device key d and the key e, and d signed that body. -/
def endpoint_signed_stmt : Prop :=
  ∀ (C : Crypto) (ops : Id → Option Op) (y c u : Id) (d e : Key),
    V C ops y (.admission c u d e) →
    ∃ x o b sg, (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧ ops x = some o ∧
      (Codec.decode o.body : Option Body) = some b ∧
      (b = .root d e sg ∨ ∃ bs, b = .request d e sg bs) ∧ C.verify d (signed o b) sg = true

/-- **A node's key is its secret's (`endpoint_derives`).** -/
def endpoint_derives_stmt : Prop :=
  ∀ (C : Crypto) (ops : Id → Option Op) (x : Id) (pk sk : ByteArray),
    V C ops x (.endpoint pk sk) → pk = cryptoSeal.pub sk ∧ sk.size = 32

/-- **The notices owed to a node (`removals_at`).** At rest,
`removalsAt c e` lists exactly the Valid removals of users with a device
admitted under e. -/
def removals_at_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key) (x : Id), Inv (family C) s → s.queue = [] →
    (x ∈ (removalsAt c e).eval s ↔ ∃ u d by_, Admitted C s.ops c u d e ∧ V C s.ops x (.removal c u by_))

/-! ## E4: a removed entry is not held -/

/-- **A removed entry is not held (`mine_not_removed`).** At rest, the
device `mine c` names is either admitted into a live user of c, or not
admitted at all (a join still waiting). -/
def mine_not_removed_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (d : Key) (a : Id), Inv (family C) s → s.queue = [] →
    (mine c).eval s = some (d, a) →
    (∃ u e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u) ∨ ∀ u e, ¬ Admitted C s.ops c u d e

/-- **Rejoining is a fresh join (`rejoin_fresh`).** At rest, if every
acceptance of the link's community held here is of a device admitted only
into removed users, and every join of it here is of an admitted device
(so none is waiting), `join` writes a fresh join: the new seed's secret,
its request, acceptance and pending join; the request is for the new
seed's device, never the removed one (`joinOps_travels`). -/
def rejoin_fresh_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (i : Invite) (seed name : ByteArray),
    Inv (family C) s → s.queue = [] →
    (∀ x d, V C s.ops x (.accepted i.community d) →
      (∃ u e, Admitted C s.ops i.community u d e) ∧
      ∀ u e, Admitted C s.ops i.community u d e → Removed C s.ops i.community u) →
    (∀ x k hs r nm d n, V C s.ops x (.joining i.community k hs r nm d n) →
      ∃ u e, Admitted C s.ops i.community u d e) →
    (∀ u e, ¬ Admitted C s.ops i.community u (Device.ofSeed seed).pk e) →
    ((join i seed name).eval s).ops = (joinOps i seed name).ops

/-- **A join never asks for an admitted device (`join_new_device`).** At
rest, every request `join` writes is for a device with no admission in
the link's community: never a removed device, whatever seed is passed. -/
def join_new_device_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (i : Invite) (seed name : ByteArray) (o : Op)
    (d e cs bs : ByteArray), Inv (family C) s → s.queue = [] →
    o ∈ ((join i seed name).eval s).ops →
    (Codec.decode o.body : Option Body) = some (.request d e cs bs) →
    ∀ u e', ¬ Admitted C s.ops i.community u d e'

/-- **Removed stays removed (`removed_stays_removed`).** Whatever is
written after, the rejoining node's new device and its admission
included, u stays removed, and every key `allowPeer` lets in is let in
for a live user other than u. -/
def removed_stays_removed_stmt : Prop :=
  ∀ (C : Crypto) (s s' : DB Fact) (c u : Id), Inv (family C) s' → s'.queue = [] →
    Extends s.ops s'.ops → Removed C s.ops c u →
    Removed C s'.ops c u ∧
      ∀ e, (allowPeer c e).eval s' = true →
        ∃ u' d, u' ≠ u ∧ Admitted C s'.ops c u' d e ∧ ¬ Removed C s'.ops c u'

end Community
