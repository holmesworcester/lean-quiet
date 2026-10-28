# Removal

What a removed member's node sees, and how it comes back: it is told its
removal once on every session open when the removal is decided, and
nothing else; then the session closes. Its node stops holding the
community, and can join again as a new device, which the members
approve like any other. This needs one change underneath: a node
handshakes with a key of its own, not with a community device key.

## Decisions (user, 2026-10-28)

- What removed members see on their devices is in scope, with designs
  and law statements first.
- The key a node handshakes with is not a device key. Then a removed
  device does not block a new device on the same node, and rejoining
  needs no special path.
- A removed member's node gets its removal and the removal's
  requirement closure, once, on each open session; after that the
  session carries nothing of the community (E1). Nothing else goes to
  it: no messages, keys, wraps or admissions beyond that closure (E2).
  This narrows the README's "no packet goes to a removed member" to its
  stated exception.
- Everything is ops and views read afresh on every step. The notice is
  a room the family's view gives, not send logic in the node.

## One device, two users

A device key may be admitted into more than one user of a community: it
signs a request under a member invitation and another under a link
invitation, or two member invitations. The rule:

**A device is live in c when it is admitted and none of the users it is
admitted into is removed. Removing any of its users cuts it, wherever
else it is admitted.** (`Live`, `Cut`.)

Why this rule, and not "the user of the least admission id":
- **Removal reaches every device of the removed user.** Under the
  least-id rule, a removed user's device stays in when its admission
  into a second user happens to have the smaller id. Ids are hashes, so
  the requester can grind for that. With this rule, `removal_cuts_off`
  needs no "admitted into no other live user" caveat.
- **Cut stays cut.** A cut device stays cut whatever arrives later
  (`cut_stays`), as a removal stays (`removed_stays`). Under the
  least-id rule, and under today's rule (live while any of its users
  is), a later admission undoes a cut: a smaller id, or one into a live
  user. Then a node holding more ops lets in a device that a node
  holding fewer has cut. Views may read absence, since they are read
  afresh; but an absence that later ops undo makes removal temporary
  for the device.
- **Only the device's consent cuts it.** A device joins a user only by
  signing that root or request (`admission_consented`). So nobody else
  can tie it to a removed user, and nobody else can cut it
  (`cut_consented`).
- **Validators do not change.** Liveness is a view's, read from lists;
  validators still read only cited facts, never an absence.
- **Coming back is a new device** (E4: `join` refuses an admitted
  device), and the node is not blocked, because another device under
  its key counts (E3).

The cost: a device linked into another person's user is cut when that
user is removed, even though its own user is live. A device that joins
a second user accepts that its access depends on both.

**Endpoint → device → user.** `allowPeer c e` reads the admissions under
key e (`admission.byKey [c, e]`); each names a device d. Device d is
live if its admissions under any key (`admission.byDevice [c, d]`)
name only users with no removal (`removal.byUser`). Key e is let in
when some device under it is live (`connect_iff`). `recipients`
(content keys are wrapped to these keys) and `members` (the dial set)
use the same device liveness. So content keys go exactly to the keys
`allowPeer` lets in (`recipients_iff`). The notices owed to a node at e
are the removals that cut its devices: every removal of every user
each of them is admitted into (`removalsAt`, `removals_at`). Holding
them, that node judges its own devices cut.

Devices are monotone and node keys are not. A node key whose devices
are all cut is let in again once a new, live device is admitted under
it: that is the rejoin.

## A node's key (E3)

**One key per node.** A node's key is an X25519 key pair kept as a local
op, `endpoint sk` (Community, like a device's `secret`): its fact is
`(pk, sk)` with `pk = X25519(sk)`, Valid iff `sk` is 32 bytes, filed
under `endpoint.all`. The first `found` or `join` on a node writes it,
from fresh bytes the caller passes; `nodeKey` reads it (the least id,
should a node ever hold two). It is never sent: local ops never travel
(`intake_local`).

**It is the key each of the node's devices names.** A root and a
request carry an X25519 key, `enc`, inside the body the device signs.
That key becomes the node's key. So the binding of a node key to a
device is the device's own consent: the root or request that admitted
it carries both keys under its signature (`endpoint_signed`, true of
the validators as they stand). Admissions are filed under their key as
well, `admission.byKey [c, e]`.

**The handshake runs on node keys.** Noise KK's statics are the two
nodes' keys; device keys only sign, and never enter Noise.
- A `request` is `(to, frm, m1)`: the responder's and the initiator's
  node keys, in the clear, and message 1. KK needs both statics in
  advance. The responder reads the initiator's key from `frm`. The
  initiator has the responder's key from the invite link
  (`Invite.inviter` is the inviter's node key), or, for a member, from
  the admissions (`recipients c`).
- `opened` and `established` cite this node's `endpoint` op, not a
  device's `secret` op. Each side runs its half with the endpoint's `sk`
  as its static and the request's other key as the peer's
  (`opened_endpoint`, `established_endpoint`). An `established` names
  its peer by node key.
- `Keys` loses the Ed25519-to-X25519 conversions; Noise's suite and
  the frames' AEAD remain.
- Ephemerals, frames, the one connection id and purge on close are
  unchanged.

**The trust rule asks about node keys.** `allowPeer c e` holds when a
device admitted under key e is live (`connect_iff`; "One device, two
users").
`trusts c me peer` keeps its shape, with `me` this node's key while it
is in c (`meV_node`). So a node whose key names a removed device is let
in again once a device of a live user is admitted under the same key
(`new_device_trusted`). That is how a removed member's node rejoins: it
writes a new device, the members approve it, and nothing else changes.
`recipients c`, the keys content keys are wrapped to, is the same set
of keys.

**Sessions** stay one per peer, and a peer is a node key. One session
between two nodes carries a room for every community both hold
(`carriedV` reads this node's communities, not the hello's). A hello
still names one community: it is the community the responder checks
trust for before answering, and the one a joiner's request rides in.
Since a session may already exist for other communities, a pending
join is dialed while its device is not admitted, not while no session
exists. The request is the same op each time, so the responder opens it
once and answers once it trusts the joiner; `kept` then keeps one of
the two sessions.

**Content keys** are wrapped to `enc`, as they are now, so to the node's
key. Every device on a node is that node's: the node holds all their
secrets already.

A member can name any key in its request, a removed node's included,
and the approvers see the key they approve. A node let in that way gets
what that member could forward to it anyway. There is no proof that the
requester holds the key's secret.

Considered and not taken:
- A separate endpoint field beside `enc` would give each device a
  second X25519 key that nothing uses: wraps and handshakes are both
  per node.
- A separate signed endpoint op could only cite the joiner's
  admission. The joiner does not have that admission until a session
  delivers it, and the session needs the binding first.

## Notice, then cut (E1, E2)

**Rooms.** The family's view, read afresh on every connection step
(`Node.refresh`), now gives a list of `Room`s: `sync c`, a community
synced both ways, as now; or `notice c x`, op x of c with its
requirement closure, given once and never taken. For each community
this node holds, and the peer key the session's `established` facts
name (`carriedV`):
- if this node is in c and the trust rule takes the peer: `sync c`;
- otherwise, a notice for each removal that cuts a device admitted
  under the peer's key (`removalsAt`) and is not yet settled on this
  session (`conn.settled`);
- otherwise nothing.

**Giving a notice** (Engine/Sync/Conn.lean). On a connection's next
`filed` step, which the node runs on every connection right after it
stores ops, or on its next `tick`, sync gives each notice it has not
given. It sends x and every stored op of x's requirement closure in c
that the peer is not known to hold, requirements first. It reports the
notice settled and records it given. Rounds, offers and wants are for
synced rooms only, so nothing is taken for a notice, and a removed
peer's ops are not asked for.

**The cut.** The node writes a local `conn.settled (cid, x)` for each
settle (`Hooks.settled`). The view then carries nothing of c for that
peer. A removal in c drops c's room and adds its notices; the session's
other communities stay as they were (`rooms_complete`). `sessions`
lists only sessions that carry something. So once a session carries
nothing, in the same entry point the node closes it, after sealing the
notice's frames, and `closing` purges it with its ops.

**Once.** A notice is given once per session: the connection records
it, the settled op takes it out of the view, and the session closes.
The trust rule refuses the removed node's key, so no new session opens
for it. A removed node with no session open when the removal is decided
is not told.

**Why give it rather than sync it.** A synced room has no end the
remover can see. The removed node stops answering once it learns its
removal, and the remover cannot tell whether it got the closure.
Giving ends when the frames are sealed.

**The removed node** receives the ops through its own synced room (it
does not know yet), and judges the removal once its closure is in.
Then `mine c` no longer holds the community (E4), so its view carries
nothing and it closes the session too.

**The bare path takes only a join.** A request's hello may carry ops.
`react` used to store every shared op of c in an opened hello, as this
node's own write, before and regardless of trust. So a removed member's
node, or anyone who knows c's id, could push posts into a member's
store with no session. Now the hello yields only what a pending join
needs: a join request of the hello's community, which reaches the
members before anyone approves it and opens nothing. Everything else
in a hello is dropped, trusted or not, since a trusted peer's ops
travel on the session (`bare_takes_only_join`).

**Two leaks closed.** A session whose view carries nothing is retired:
`sessions` and `retired` read the view, so a removed peer's session does
not stay open with no rooms. `onArrival` re-sends a request's answer
only if the trust rule takes its initiator (`resend_trusted`). `react`
already answers only the trusted (`answer_trusted`, now stated).

## A removed entry is not held (E4)

- `Community.mine c` skips an acceptance whose device is cut
  (`mine_not_removed`). A device that is not admitted still counts
  while one of its joins waits.
- A join to resume is one whose device was never admitted. A removed
  device's join is spent, so `join` writes a fresh join: a new device
  from the new seed, whose request carries the node's key
  (`rejoin_fresh`). `join` writes nothing for a seed whose device is
  already admitted in c, so it never asks for a removed device
  (`join_new_device`).
- The old user stays removed whatever follows, every device ever
  admitted into it stays cut, and `allowPeer` lets a key in only for a
  live device that was never the old user's (`removed_stays_removed`).

## Changes to code others own

- **Engine/Sync/Node.lean, one line**: `Hooks.rooms : Id → m (List Room)`,
  was `List Id`. `Node.refresh` and `Node.open` pass the rooms through
  as they are. The reason: a notice is per-step data from the family,
  and `rooms` is the only per-step channel from the family to a
  connection. The alternative that leaves Node.lean alone encodes a
  notice as a room id, `encode (c, x)` beside 32-byte community ids,
  which Conn would decode. That is a typed value hidden in bytes, so it
  is not proposed.
- **Engine/Sync/Conn.lean**: `Room`, `Conn.notices`, `setRooms` taking
  rooms, the notice walk (`closureOps`), `give` and `notify`, called by
  `filed` and `tick`. In ConnLaws, `filed_send` and `tick_send` become
  `notice_send`; `recv_send` and `recv_take` stand.
- **Engine/Sync/Pair.lean, Tests/SyncPair, Tests/TcpPair**: `rooms`
  hooks give `[.sync c]`.
- **Connection/RoomLaws.lean**: `rooms_trusted`, `rooms_cut` and
  `rooms_model` are restated over `sync c`.
- **Community/Query.lean and Connect.lean**: `live` counts an admission
  only if its device is live, so `allowPeer` (now by key), `members` and
  `recipients` follow the rule. `connect_iff`, `refuse_nonmember`,
  `removal_cuts_off`, `connect_admitted`, `members_iff` and
  `recipients_iff` are restated, and the README's "admitted into no
  other live user" caveat goes.

## Laws

Statements are in Engine/Sync/NoticeLaws.lean,
Connection/RemovalLaws.lean and Community/RemovalLaws.lean, each a
`_stmt : Prop`, all over the code that runs: Conn's steps on the
model, the views, the validators and the intents.

| question | law |
|---|---|
| Which devices does a removal cut, and for how long? | `removal_cuts_off`, `cut_stays`, `cut_consented` |
| Is the notice given, once? | `notice_sent`, `notice_once`, `closure` |
| Does a step send anything but notices? | `notice_send` |
| What does a removed member's session carry? | `rooms_removed` |
| What reaches a removed member's node? | `removed_gets_only_notice` |
| Is the session then closed? | `notice_then_cut` |
| Does a removed node get a new session or a re-sent answer? | `answer_trusted`, `resend_trusted` |
| Can anyone push ops in without a session? | `bare_takes_only_join` |
| Does a removal in c disturb the session's other communities? | `rooms_complete` |
| Whose keys does the handshake run on? | `opened_endpoint`, `established_endpoint`, `endpoint_derives` |
| How is a node key tied to a device? | `endpoint_signed` |
| Whom does the trust rule let in, dial, and seal to? | `connect_iff`, `refuse_nonmember`, `connect_admitted`, `new_device_trusted`, `meV_node`, `members_iff`, `recipients_iff` |
| Which removals is a node owed? | `removals_at` |
| Does a removed node still hold the community? | `mine_not_removed` |
| How does it rejoin? | `rejoin_fresh`, `join_new_device` |
| Can a rejoin undo the removal? | `removed_stays_removed` |

The connection-step laws take the connection as `Node.refresh` leaves
it, `c.setRooms ((roomsV cid).eval s)` (`rooms_model`), and Conn's
`recv`, `filed`, `tick` and `open` run on it: the steps `Node.onFrame`,
`Node.fanout` and `Node.onTick` run. Their premises are read from the
lists of the node's own store, as `rooms_cut`'s are.

## Tests

- `lifecycle`: A founds and admits B; A removes B; B takes the removal
  from A's offer; B's `mine` drops the community. B joins again from a
  new link, and the request is for a new device with B's node key. A
  approves, and B is admitted under a new user; the old user stays
  removed, and `allowPeer` lets B's node in.
- `jointcp`, over localhost TCP: A removes B while their session is
  live. B receives the removal and its closure and nothing after it,
  and both ends close the session. The removed B then dials A with a
  fresh post in its hello; A stores neither the post nor anything but a
  join request. B's node rejoins with a new device and is admitted
  again once A approves; a post then reaches B.
- Negative controls, each failing a check: a `rooms` hook without
  notices (B never learns its removal); `sessions` not reading the view
  (A keeps the session open); a `react` that also stores the rest of a
  hello, as it used to (A stores B's post).

## Not covered

- An entry point as a whole: the laws are per connection step. The
  composition (refresh, step, settle, follow, seal, purge) is tested,
  not proven.
- Community's laws hold over a Community store. Their premises on the
  node's composed store are read from its lists, as `rooms_cut` does;
  carrying a Community law to the composed store (`sum_project`) is
  still to prove.
- Sync wire ops (round claims, have, want) name ids of synced rooms or
  ids the peer sent. That is tested, not proven (`have_shown` in
  SYNC.md).
- A removed member's node keeps what it already holds; content keys are
  not rotated.
