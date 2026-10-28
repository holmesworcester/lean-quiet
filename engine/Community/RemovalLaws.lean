/-
The Community side of docs/REMOVAL.md, stated of the views and intents
that run, at rest (queue empty) over the persisted tables. Statements
(`_stmt`), proven in phase 2.

One device, two users: a device may be admitted into several users of
c. It is live (`Live`) when it is admitted and none of those users is
removed; removing any of them cuts it (`Cut`), wherever else it is
admitted. Liveness is a view's; validators are untouched.
- `cut_stays_stmt`: a cut device stays cut whatever arrives later.
- `cut_consented_stmt`: only the device's own consent ties it to a
  user, so only a removal of a user it signed into cuts it.

E3, a node's key:
- `connect_iff_stmt`, `refuse_nonmember_stmt`, `removal_cuts_off_stmt`,
  `connect_admitted_stmt`: `allowPeer c e` asks about a node's key e (an
  admission's X25519 key, which the node's handshake runs on), and lets
  it in exactly when a device admitted under e is live. These replace
  `connect_iff`, `refuse_nonmember`, `removal_cuts_off` and
  `connect_admitted`, which asked about device keys and counted a
  device while any of its users was live.
- `recipients_iff_stmt`, `members_iff_stmt`: content keys are wrapped to
  exactly the keys `allowPeer` lets in, and the dial set is the live
  devices. `connect_agree` stands as it is.
- `new_device_trusted_stmt`: so a removed user's device does not block
  a new device on the same node: one live device under e is enough.
- `endpoint_signed_stmt`: the binding. An admission's key was signed by
  its device: the root or request it came from carries both, signed by
  the device. (True of the code today; it becomes the binding once e
  is the node's key.)
- `endpoint_derives_stmt`: a Valid endpoint fact's key is its secret's.
- `removals_at_stmt`: `removalsAt c e` lists exactly the removals that
  cut the devices admitted under e: the notices owed to the node at e.

E4, a removed entry is not held:
- `mine_not_removed_stmt`: `mine c` never names a cut device.
- `rejoin_fresh_stmt`: after removal, `join` writes a fresh join for
  the new device's seed (phase 2: plus the node key, `fresh`).
- `join_new_device_stmt`: a join never asks for a device already
  admitted in the community, so never for a removed one.
- `removed_stays_removed_stmt`: whatever is written after, u stays
  removed, every device of u stays cut, and no key is let in for one.
-/
import Community.Intents

namespace Community
open Engine

/-! ## One device, two users -/

section
variable (C : Crypto) (ops : Id → Option Op)

/-- Device d is live in c: admitted, and none of the users it is
admitted into (under any key) removed. -/
def Live (c : Id) (d : Key) : Prop :=
  (∃ u e, Admitted C ops c u d e) ∧ ∀ u e, Admitted C ops c u d e → ¬ Removed C ops c u

/-- Device d is cut in c: admitted into a user that is removed. -/
def Cut (c : Id) (d : Key) : Prop := ∃ u e, Admitted C ops c u d e ∧ Removed C ops c u

end

/-- **Cut stays cut (`cut_stays`).** More ops never make a cut device
live again: no later admission, of any id into any user, undoes it. -/
def cut_stays_stmt : Prop :=
  ∀ (C : Crypto) (ops ops' : Id → Option Op) (c : Id) (d : Key),
    Extends ops ops' → Cut C ops c d → Cut C ops' c d ∧ ¬ Live C ops' c d

/-- **Only a device's own consent cuts it (`cut_consented`).** A cut
device signed the root or request that admitted it into the removed
user: nobody else can tie it to a user, so nobody else can cut it. -/
def cut_consented_stmt : Prop :=
  ∀ (C : Crypto) (ops : Id → Option Op) (c : Id) (d : Key), Cut C ops c d →
    ∃ u e y x o b sg, V C ops y (.admission c u d e) ∧ Removed C ops c u ∧
      (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧ ops x = some o ∧
      (Codec.decode o.body : Option Body) = some b ∧
      (b = .root d e sg ∨ ∃ bs, b = .request d e sg bs) ∧ C.verify d (signed o b) sg = true

/-! ## E3: a node's key -/

/-- **Who we connect to, by node key (`connect_iff`).** At rest,
`allowPeer c e` accepts key e exactly when some device admitted under e
is live. -/
def connect_iff_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key), Inv (family C) s → s.queue = [] →
    ((allowPeer c e).eval s = true ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d)

/-- **No connection to a node with no live device (`refuse_nonmember`).** -/
def refuse_nonmember_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key), Inv (family C) s → s.queue = [] →
    (∀ u d, Admitted C s.ops c u d e → Cut C s.ops c d) → (allowPeer c e).eval s = false

/-- **A removal cuts off the removed user's node (`removal_cuts_off`).**
Every device of u is cut, wherever else it is admitted; so a node whose
key names only u's devices is refused. (A node is let in again only
through a live device under its key: `new_device_trusted`.) -/
def removal_cuts_off_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c u : Id) (e : Key), Inv (family C) s → s.queue = [] →
    Removed C s.ops c u →
    (∀ u' d, Admitted C s.ops c u' d e → ∃ e', Admitted C s.ops c u d e') →
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
    (∀ u' e', Admitted C s.ops c u' d e' → ¬ Removed C s.ops c u') → (allowPeer c e).eval s = true

/-- **A new device on a removed user's node is let in
(`new_device_trusted`).** A node whose key names a removed user's device
is let in once a live device is admitted under the same key: the cut
device does not block the node. -/
def new_device_trusted_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c u u2 : Id) (d d2 e : Key), Inv (family C) s → s.queue = [] →
    Admitted C s.ops c u d e → Removed C s.ops c u →
    Admitted C s.ops c u2 d2 e → Live C s.ops c d2 → (allowPeer c e).eval s = true

/-- **Content keys go exactly where connections go (`recipients_iff`).**
At rest, `recipients c` names exactly the keys with a live device: the
keys `allowPeer` lets in. -/
def recipients_iff_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key), Inv (family C) s → s.queue = [] →
    (e ∈ (recipients c).eval s ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d)

/-- **The dial set is the live devices (`members_iff`).** -/
def members_iff_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (d : Key), Inv (family C) s → s.queue = [] →
    (d ∈ (members c).eval s ↔ Live C s.ops c d)

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
`removalsAt c e` lists exactly the Valid removals that cut a device
admitted under e: removals of any user such a device is admitted into,
under any key. -/
def removals_at_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (e : Key) (x : Id), Inv (family C) s → s.queue = [] →
    (x ∈ (removalsAt c e).eval s ↔
      ∃ u0 d u e' by_, Admitted C s.ops c u0 d e ∧ Admitted C s.ops c u d e' ∧
        V C s.ops x (.removal c u by_))

/-! ## E4: a removed entry is not held -/

/-- **A removed entry is not held (`mine_not_removed`).** At rest, the
device `mine c` names is live, or not admitted at all (a join still
waiting): never a cut device. -/
def mine_not_removed_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (c : Id) (d : Key) (a : Id), Inv (family C) s → s.queue = [] →
    (mine c).eval s = some (d, a) → Live C s.ops c d ∨ ∀ u e, ¬ Admitted C s.ops c u d e

/-- **Rejoining is a fresh join (`rejoin_fresh`).** At rest, if every
acceptance of the link's community held here is of a cut device, every
join of it here is of an admitted device (so none is waiting), and the
new seed's device is not admitted, `join` writes a fresh join: the new
seed's secret, its request, acceptance and pending join; the request is
for the new seed's device, never the cut one (`joinOps_travels`). -/
def rejoin_fresh_stmt : Prop :=
  ∀ (C : Crypto) (s : DB Fact) (i : Invite) (seed name : ByteArray),
    Inv (family C) s → s.queue = [] →
    (∀ x d, V C s.ops x (.accepted i.community d) → Cut C s.ops i.community d) →
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
included: u stays removed, every device ever admitted into u is cut, and
every key `allowPeer` lets in is let in for a live device that was never
u's. -/
def removed_stays_removed_stmt : Prop :=
  ∀ (C : Crypto) (s s' : DB Fact) (c u : Id), Inv (family C) s' → s'.queue = [] →
    Extends s.ops s'.ops → Removed C s.ops c u →
    Removed C s'.ops c u ∧
      (∀ d e, Admitted C s'.ops c u d e → Cut C s'.ops c d ∧ ¬ Live C s'.ops c d) ∧
      ∀ e, (allowPeer c e).eval s' = true →
        ∃ u' d, Admitted C s'.ops c u' d e ∧ Live C s'.ops c d ∧ ∀ e', ¬ Admitted C s'.ops c u d e'

end Community
