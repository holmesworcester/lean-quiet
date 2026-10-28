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
(`roomsV` reads this node's communities, not the hello's). A hello
still names one community: it is the community the responder checks
trust for before answering, and the one a joiner's request rides in.
Since a session may already exist for other communities, a pending
join is sent until a connection answers its request, beside an open
session or not (`rejoin_dials`); an admitted join is dialed again only
while no session is open (`reconnect_dials`). The request is the one
whose hello delivers the join's request, the same op each time, so the
responder opens it once and answers once it trusts the joiner; `kept`
then keeps one of the two sessions.

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
name (`roomsV`):
- if this node is in c and the trust rule takes the peer: `sync c`;
- otherwise, a notice for each removal that cuts a device admitted
  under the peer's key (`removalsAt`) and is not yet given on this
  session (`conn.given`);
- otherwise nothing.

**Giving a notice** (ops/sync/Notice.lean). `Hooks.rooms` gives the
connection its typed rooms, and `Node.refresh` carries them: the synced
rooms as before, and the notices. A connection has its own `given`
field and `Status.given`. `notify` gives each notice not given yet: it
sends x and every stored op of x's requirement closure in c that the
peer is not known to hold, requirements first (`closureOps`, at most
`cfg.walk` ops). It records x in `given` and reports `given x`. The node
runs it on every connection where it runs `filed`, right after it
stores ops (`filedGive`), and where it runs `tick` (`tickGive`, unless
the tick drops the session). `filed` and `tick` themselves stay sync
only (`filed_send`, `tick_send`, `have_shown`). Rounds, offers and wants
are for synced rooms only, so nothing is taken for a notice, a have for
c gets no reply (`notice_no_holds`), and a removed peer's ops are not
asked for.

**The cut.** The node writes a local `conn.given (cid, x)` for each
notice given: the settle hook takes the step's statuses, and writes
`given` for a notice and nothing for a room's settle. The view then carries
nothing of c for that peer. A removal in c drops c's room and adds its notices; the session's
other communities stay as they were (`rooms_complete`). `sessions`
lists only sessions that carry something. So once a session carries
nothing, in the same entry point the node closes it, after sealing the
notice's frames, and `closing` purges it with its ops. The runner sends
an entry point's frames before it closes the sockets of the sessions
that entry point dropped, so the notice reaches the peer before the
connection's end does; a socket closes once no session is left on it.

**Once.** A notice is given once per session: the connection records
it, the `given` op takes it out of the view, and the session closes.
The trust rule refuses the removed node's key, so no new session opens
for it: a redial by the removed node gets no answer (`answer_trusted`,
`resend_trusted`). A removed node with no session open when the removal
is decided is not told.

**Why `given` is an op.** The rooms view decides what a session
carries, and it reads only ops. Without a record that the notice was
given, the view would carry the notice for as long as the session
lives: the session would never carry nothing, so it would never close,
and the notice would be given again whenever the session's connection
is made afresh from its ops (a restart reopens a session from its
`established`, with a new connection whose memory holds nothing). A
connection's memory alone cannot end the session, since the view, not
the connection, decides what it carries. The op cites the connection,
so it lives exactly as long as the session.

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

## Status

Built and proven, on lq main's layout:
- **E3**, the node's key: `endpoint` ops, roots and requests naming it,
  `admission.byKey`, the handshake ops on node keys, `allowPeer` by
  key with device liveness, and the trust rule, rooms and dial on node
  keys. Laws: `opened_endpoint`, `established_endpoint`,
  `established_agrees` (restated), `endpoint_signed`, `endpoint_derives`,
  `meV_node`, `connect_iff` and its kin (restated), `new_device_trusted`,
  `rooms_trusted`, `rooms_cut` (restated over peer keys).
- **One device, two users**: `Live`, `Cut`, `deviceLive_iff`,
  `cut_stays`, `cut_consented`, `removals_at`; the people list follows it
  (`present_iff` restated, `present_not_removed`).
- **E4**: `mine` skips a cut device, `join` resumes only a never-admitted
  join and refuses an admitted seed, and `introduce` names this device's
  join. Laws: `mine_not_removed`, `rejoin_fresh`, `join_new_device`,
  `removed_stays_removed`. Tested in `lifecycle`.
- **Dialing a join**: a pending join of this node's own entry is sent as
  the request whose hello delivers the join's request, while its device
  is not admitted, until a connection answers it, beside an open
  session or not; once admitted, while no session to the inviter is
  open. Laws: `rejoin_dials`, `reconnect_dials`. Tested in `jointcp`: B,
  removed from c but sharing another community with A over one open
  session, rejoins c as a new device; negative control: the rule before
  (skip while a session is open and the inviter is let in) would not
  send it.
- **The bare path** (E2's other side): `react` takes only join requests
  from a hello, answers only the trusted, and `onArrival` re-sends only
  to the trusted. Laws: `bare_takes_only_join`, `answer_trusted`,
  `resend_trusted`. Tested in `jointcp`, with the negative control.
- **One session per node key**, carrying every community both nodes
  hold. Tested in `connection_check`: a second community's join beside
  an open session, approved and synced over one session.
- **The rooms view**, typed: `roomsV` gives `.sync c` or `.notice c x`
  per (held community, peer key); the `rooms` hook gives it to the node
  as it is. `sessions` and `retired` read it, so a
  session that carries nothing is retired. Laws: `rooms_trusted`,
  `rooms_cut` (no `.sync c` for a refused peer), `rooms_model`,
  `rooms_removed`, `rooms_complete`, `notice_then_cut`.
- **Notice, then cut** (E1, E2): typed rooms in `Hooks.rooms`, `Conn`'s
  own `given` and `Status.given`, `notify` run with `filed` and `tick`
  (`filedGive`, `tickGive`), the settle hook writing `conn.given`, and
  the runner sending a step's frames before it closes the dropped
  sessions' sockets. Laws: `closure`, `notice_sent`, `notice_send`,
  `notice_once`, `notice_no_holds`, `removed_gets_only_notice`;
  `rooms_model` restated over typed rooms. `filed_send`, `tick_send`,
  `have_shown` and `hold_reply_local` stand as they were. Tested in
  `connection_check` (in memory) and `jointcp` (TCP): A removes B on a
  live session, B is told, both ends close and purge the session, and B
  rejoins as a new device; with a second community shared, the session
  stays open for it. Negative controls in both: a rooms hook with no
  notices (B never learns its removal), and sessions that do not read
  the rooms view (the session stays open).

Found on the way, in Conn (a3's):
- A session carries a room on one side only while the other does not
  trust yet (a joiner's link clause on a session open for other
  communities). The dialer's rounds for it go unanswered, and patience
  may drop the session. A responder could end a round for a room it
  does not carry.
- A dialer dropped a healthy session at its first round after a quiet
  spell longer than `patience`: fixed by a3/sync-harden (patience runs
  from when the wait began).
- The runner closed every socket at a dropped session's address, so
  retiring one of two sessions on a socket (a join sent beside an open
  session) killed the other, then the redials, without end. It now
  closes a socket once no session is left on it.

## Changes to code others own

- **engine/wire/Node.lean**: `Hooks.rooms : Id → m (List Room)`, was
  `List Id`, and the settle hook takes the step's `Status`. The reason:
  a notice is per-step data from the family, and `rooms` is the only
  per-step channel from the family to a connection (encoding a notice as
  a room id would hide a typed value in bytes). `Node.refresh` carries
  the rooms (`Conn.carry`); `Node.open` opens on the synced ones; the
  node runs `filedGive` where it ran `filed` and `tickGive` where it ran
  `tick`.
- **engine/wire/Tcp.lean**: the runner sends a step's frames, then
  closes the sockets of the sessions the step dropped, and a socket only
  once no session is left on it.
- **ops/sync/Conn.lean**: `notices` and `given` fields, `Status.given`.
  `filed` and `tick` are unchanged; ops/sync/Notice.lean holds `Room`,
  `carry`, `closureOps`, `give`, `notify`, `filedGive`, `tickGive`. In
  ConnLaws, `filed_send`, `tick_send`, `recv_send` and `recv_take`
  stand, and OfferLaws' `have_shown` and `hold_reply_local` stand.
- **engine/wire/World.lean and WorldLaws.lean**: the world's rooms hook
  gives `.sync` rooms; the stream laws carry the refreshed connection
  (no notices) through, with `filedGive_quiet` and Reads lemmas for the
  notice code.
- **tests/engine SyncPair, TcpPair, HardenLib**: `rooms` hooks give
  `.sync` rooms.
- **ops/connection/RoomLaws.lean**: `rooms_trusted`, `rooms_cut` are
  restated over `sync c`; `rooms_model` over typed rooms.
- **ops/community/Query.lean and Connect.lean**: `live` counts an admission
  only if its device is live, so `allowPeer` (now by key), `members` and
  `recipients` follow the rule. `connect_iff`, `refuse_nonmember`,
  `removal_cuts_off`, `connect_admitted`, `members_iff` and
  `recipients_iff` are restated, and the README's "admitted into no
  other live user" caveat goes.

## Laws

In ops/sync/NoticeLaws.lean, ops/connection/RemovalLaws.lean,
ops/community/RemovalLaws.lean and ops/community/Connect.lean, all over
the code that runs: Conn's steps on the model, the views, the
validators and the intents. All are theorems in the axiom audit.

| question | law |
|---|---|
| Which devices does a removal cut, and for how long? | `removal_cuts_off`, `cut_stays`, `cut_consented` |
| Is the notice given, once? | `notice_sent`, `notice_once`, `closure` |
| Does a step send anything but notices? | `notice_send` |
| Does a removed member learn what this node holds of c? | `notice_no_holds` |
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
it, `c.carry ((roomsV cid).eval s)` (`rooms_model`), and Conn's `recv`,
`filedGive`, `tickGive` and `open` run on it: the steps `Node.onFrame`,
`Node.fanout` and `Node.onTick` run. Their premises are read from the
lists of the node's own store, as `rooms_cut`'s are.

## Tests

- `lifecycle` (done): A removes C; C takes the removal from A's offer;
  C's device is cut and its `mine` drops the community; a join with the
  cut seed writes nothing. C joins again from a new link, and the
  request is for a new device with C's node key. A refuses C's node
  until it approves, then lets it in; C is admitted under a new user;
  the old user stays removed and the old device stays cut, on both.
- `connection_check` (in memory, done): A removes B on a live session;
  B is told (it holds its removal, which only the notice carries), and
  both ends close; negative controls: a rooms hook with no notices (B
  never learns, A keeps the session open), sessions not reading the
  view (B is told, neither side closes).
- `jointcp`, over localhost TCP (done): sessions name node keys, never
  device keys. A removes B while their session is live and carries only
  that community: B is told, its device is cut, both ends close and
  purge the session, nothing reopens, and a later post of A's does not
  reach B. The removed B dials A with a fresh post in its hello; A opens
  the request, stores no post, and answers nothing (negative control:
  the deliver step before the fix takes it). B rejoins as a new device
  under its node key, refused until A approves it. With a second
  community shared, a second removal leaves the session open for it,
  and B rejoins beside the open session (negative control: the dial
  rule before the fix). Negative controls on runner pairs with mutated
  hooks: a rooms hook with no notices (B never learns its removal) and
  sessions not reading the view (the session stays open at both ends).
  With the runner closing a dropped session's socket before sending its
  frames, B is never told.

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
