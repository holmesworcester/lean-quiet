# Sync

How two nodes come to hold the same ops: range-based set reconciliation
(RBSR) with Merkle fingerprints, a stream of new ops between rounds, and
requirement closures for windowed nodes. Sync is engine code (it knows
nothing of communities); everything protocol-specific (the handshake,
which rooms a peer may see, arrival records) comes from op families
through `Hooks`.

## Decisions (user, 2026-10-27)

- Ops are wire bytes: an op's id is the SHA-256 of the bytes received,
  decoding is strict, and the same bytes are stored (`Op.id_decode`).
- RBSR, not RIBLT, "for provability": termination and completeness are
  deterministic.
- "True Merkle RBSR" as in Meyer and Scherer, *Range-Based Set
  Reconciliation Without Homomorphic Hashing* (2025): a range's
  fingerprint is its count and the Merkle label of its items' canonical
  treap. No XOR or sum fingerprint (forgeable by a member grinding ids,
  Meyer 2023 §5.2).
- The sync set is the ops table without local ops: `Scope` is
  `shared room | conn | local`; only shared ops sync, in their room.
- Ranges are over an op's claimed time (`Family.order`), "because that's
  semantically relevant to the user", never over received-at.
- Windowed nodes now: a node may keep only ops from a floor of claimed
  time on, plus everything they require.
- The tree is kept in memory. Grinding a degenerate treap (Meyer 2023
  §6.3, compute only) is accepted, with caps.
- Sync messages are three op kinds: `sync.rbsr` (claims back and forth),
  `sync.have` and `sync.want` (independent of rounds, and also the
  stream).
- The handshake is ops the engine handles, as in poc-17 (holmes-fd's
  Connection family).
- Frames follow poc-17. A frame names its session and opens only under
  that session's keys, with a random nonce, so no side keeps sealer
  state. A replayed frame re-delivers ops, and ops are idempotent.
  Sockets are not bound to sessions.
- All state is ops, except the sockets at the seam and caches derived
  from ops (docs/LAYOUT.md). This is a planned conversion; see
  "Planned" below.
- A dropped session is never reopened; a new connection needs a new
  handshake.
- The family hears every arrival (`recv`), a repeat included, so it can
  answer a replayed request again (poc-17's healing for a lost answer).
- Engine code and op code are strictly separate, and code that is
  neither is kept to a minimum: the daemon is sockets, timers and
  discovery; everything else is the engine's driver (`Node`) or a
  family's ops.

Papers and the poc survey behind these: `/mnt/storage/holmes-research/rbsr/`.

## Notice delivery after the simplification

`Hooks.rooms` still returns typed `List Room`: `Room.sync r` permits sync;
`Room.notice r x` permits only the removal notice and its requirement
closure. `Conn.carry` refreshes these separately on every node step.
The per-room snapshots and gates operate only on `Room.syncs`.

The delivery result has one field, `Step.given : List Id`, beside send and
take. `Conn.given` suppresses repeats on this connection. `Step.then`
concatenates the results; `filedGive` and `tickGive` retain their order.
`Node.recordGiven` passes each `(connection, notice)` to
`Hooks.onGiven : Id → Id → List Op`; Connection returns the same local
`Given.op` as before. The next rooms read excludes that notice, and a
session with no remaining rooms is retired. This is a local record of
handing out the notice, not a remote acknowledgment. It needs no generic
status sum, settled room, or completion report.

The notice laws keep their premises and conclusions: keyed ops, the
carried notice not already given, one room per notice, its closure fitting
`cfg.walk`, and (for tick delivery) a tick that does not drop. `Gives` now
reads `x ∈ st.given` where it read `Status.given x ∈ st.status`; its
connection-history and full closure-delivery conjuncts are unchanged.
The tick's non-drop premise now means `now ≤ c.heard + cfg.live`.
No removal-law premise is added, and all 24 pinned removal laws keep
their statements. Notice delivery preserves phase and heard time
(`give_shape`); `honest_no_drop`, `handlers_transition` and
`closed_terminal` also cover carry, notify, filedGive and tickGive.

## Model

**Items and keys.** A room's sync set is its stored shared ops. Each is
an item `(key, id)` with `key = (claimed time, num id)`; `num` reads the
id as a number and is injective (`num_inj`), so keys name items.

**Ranges and windows.** A range is `[lo, hi)` over keys. A window from
floor `f` is every op with no claimed time (roots, invitations,
admissions, removals: structure, including every removal a node needs
to refuse a removed peer) and every op claimed at `f` or later:
`[0, 1) ∪ [f, ∞)`, one range when `f ≤ 1`. A round runs over the
overlap of the two sides' windows.

**Fingerprints.** `fp l = (|l|, lbl l)`. `lbl` is the Merkle label of
the canonical treap of `l`: the item with the largest id number at the
root, smaller keys left, larger right; `lbl [] = h ""`,
`lbl node = h (encode (lbl left, id, lbl right))`. It reads the set only
through `top` and `filter`, so it is a function of the set.

**Rounds** (Meyer 2023, Protocol 1). A claim is a range's fingerprint or
all of the claimant's ids in it. `answer` (ops/sync/Round.lean):
- a matching fingerprint settles the range;
- if this side holds `leaf` (128) items or fewer there, it answers with
  its ids;
- otherwise it cuts the range into up to `fan` (16) pieces of nearly
  equal count and claims each by its fingerprint;
- a claim of ids is answered with what this side holds there that the
  claimant lacks (`hold`) and what it lacks (`want`).

Each side answers a round's claims from a snapshot of the room taken
when it first saw the round. A message with no claims ends the round.

**Have and want.** `hold` goes out as `sync.have`, naming its room (the
round's, or each offered op's). The peer wants what it lacks in that
room (`sync.want`), and wanted ops are sent as their own bytes. A want
for an id outside the connection's rooms, a local or conn op, or an
unknown id, is ignored silently. `authorize ix c ids` filters ids against
only the connection's shown rooms in the index before `Store.getOp`.
The read program `serve` reads only that list, stopping after the first
whole op that reaches `wantBytes` (4 MiB by default); encoded op payloads
are bounded by `wantBytes` plus one op, excluding transport envelopes.
The store outside those rooms changes neither the read sequence nor the
reply. Closure reads are deferred to ticks. The receiver retains admitted unsatisfied ids in `asked`. Every `retry` ms
(1000 by default) a tick re-wants at most `maxIds` of them. Each ask expires
strictly after its original ask time plus `askTime`; repeat offers and
retries do not renew that time. Expiry frees capacity even if other peer
traffic keeps the session alive. Later rounds or offers rediscover deferred
or expired ids, so a byte-limited response does not abandon the rest forever. A have for a room the peer may not see
is ignored, and a have is answered from that room's ops only, so a
peer's haves learn nothing of other rooms or of local ops.

**Stream.** Between rounds, each op newly stored is offered
(`sync.have`) on every connection whose peer may see it and is not known
to hold it. The stream is only ever safe (laws below). Liveness comes
from rounds.

**Closure.** A full-range round (`max floor peerFloor ≤ 1`) keeps no
sender per-op bookkeeping: neither its holds nor served wants add to
`offered`, `closed`, or `frontier`. RBSR reconciles the entire room,
requirements included (`exchange_complete`, `ends_log`). Each round
captures its overlap floor in `roundFloor` alongside its room snapshots;
all rooms in that round share that window. The captured floor survives
the empty end, so delayed wants do not consult a later hello. Wants have
no round id on the wire; they use the connection's latest captured round.
Honest peers keep their negotiated floors fixed during a session.

Only a windowed round (`roundFloor > 1`) queues the requirements of
served ops. `closureCap` (4096 ids by default) bounds **visited plus
pending** distinct requirement ids (`closed.size + frontier.length`).
Repeated requirements consume no additional slots. The cap is shared by
all rooms in the round, so a connection's total closure state is bounded.
Closure uses no share of `offered`: visited ids record its deduplication.
A tick visits at most `walk` admitted ids. The walk records each visited
id, including missing or invalid ops, and a new round clears visited,
pending, and the cut flag before retrying from that round's served ops.

Admission keeps only the prefix that fits and sets `Conn.closureCut` on
overflow. The local app can inspect that flag on its Node connection;
it stays set for that round. Admitted work drains on later ticks, but no
additional distinct id fits after a cut. Discarded ids are never marked
visited or promised as closure offers. A windowed receiver then lacks
some older requirements and their transitive dependencies: some received
ops remain Missing, so agreement with the full peer holds only for ops
whose verdict dependencies it actually holds (`spec_local`). The flag
is local to the sender; with no wire change the receiver gets no remote
cut notification. There is no settled status. Completion checks compare the actual stored
room ops; a round ending does not certify closure completeness.

When the entire stored, shown requirement closure fits, the walk offers
all its ids not already advertised or known held by the peer. The
completeness law uses any finite requirement-closed superset of the
served ops' requirement seeds as a size witness, distinct initial
pending ids, no previously visited ids, and enough walk fuel to visit
that set. The witness is proof data, not another runtime cache.

`offered` now belongs only to live stream deduplication. Like `known`,
it uses `remember maxKnown`: when an insertion would exceed the cap,
it forgets old hints and retains the new id (zero disables hints). The
cost of forgetting is a repeated have, never a lost op or a dropped session.

**Proposal only: receiver-driven missing requirements.** A future
windowed receiver could inspect the requirements of each stored Missing
op and request absent ids with existing wants. The sender would serve
authorized ids without walking or retaining closure state, even for
windows. This is not implemented: today's receiver asks only for ids
advertised in rounds or haves. It would require bounded scheduling,
deduplication, retries and fair discovery at the receiver, plus a rule
for absent or out-of-room requirements. Chains cost additional network
round trips and store reads; batching helps breadth but cannot remove
serial dependency latency. A peer would learn which specific requirement
ids the receiver lacks, and could infer dependency interests and partial
possession, beyond the ordinary overlap fingerprints. Authorization must
still precede blob reads; requests must not probe unrelated rooms.
The user decides whether to change sync behavior this way.

**Liveness.** Both roles drop exactly when `heard + live < now`.
`live` defaults to 90000 ms. Each decoded op refreshes `heard`. A tick
with no other output sends an empty `have` after `live/3` without sending;
Node records the outgoing time for all payloads, including local writes.
With positive `live/3`, each side ticking at least that often and frames
delivered within that interval never drops: `live_stays` inducts over
tick histories, using the scheduler's preceding tick and delivery of its
output (or the earlier output remembered in `sent`). The scheduler and
transport guarantees are assumptions, not properties of the OS.
Opening a round does not refresh peer liveness. An unserved ask expires
after `askTime` (20000 ms), even while keepalives arrive, freeing `asked`
without closing the session. Logical time has no pause accounting.

**Independent rooms.** A cadence starts only rooms without their own
snapshot; another room in flight cannot gate them. An unshown room gets
an empty end without changing the connection. Snapshot and closure caps
still apply across the connection; this is not a fairness or CPU bound.

**Session phases.** A fresh connection goes from Dialing to Hello; the
peer's hello advances it to Live. Timeout enters Closed. Every handler
respects the transition relation, and Closed cannot become another phase.
Node removes ended connections and remembers their ids against reopening;
a fresh session needs a fresh handshake.
The responder answers the dialer's hello with its own window. Its first
hello can have arrived before the dialer got session keys if the bare
handshake answer was lost; this reply completes sync without a redial.

**Every end purges.** TCP EOF, errors, oversized framing, idle closure,
send failure and runner stop notify `Node.onClose` with the socket's
address. All sessions currently routed through it drop. The common
`Node.finish` path runs `closing` then `Turn.purge fam ids true` for
transport drops, silence expiry, sessions removed
from `established`, and retirement. Retired sessions leave memory too.
A closed session cannot reopen; a new handshake is needed.

**Peer-controlled storage.** `RunConfig.queue` (64) bounds queued events;
readers block on a full queue, carrying TCP backpressure to the peer.
Each inbound frame is at most 1 MiB. Reads stop at the current frame's
boundary: each socket holds one assembling or blocked frame, plus a
read of at most 64 KiB. Slots are reserved before accepting into the
queue or dialing: at most `maxSocks` (64) in total and `perAddr` (4) per
IP, ignoring source port (`peerHost`: an address's text without its
port, `[addr]` for IPv6). Extra accepts close immediately. The listener
binds IPv4 only today, and dials parse IPv4 only.
Pending outbound dials keep at most `max 1 queue` payloads per address;
overflow closes the session.

`known`, `asked`, and stream `offered` each hold at most `maxKnown`
(65536) ids: together at most `3 * maxKnown` ids per connection, plus a timestamp per outstanding
ask (a parallel map whose entries leave with their asks). Inserting a new
`known` hint that would exceed the cap clears old hints, then remembers the
new id. Redundant offers are harmless. A full `asked` admits no more missing
ids, sends no wants for them and does not add them to `known`; later rounds
or offers bring them again. Neither case is a protocol violation or ends
the session. A zero cap retains no hints or asks. `hold` checks `maxIds`
before reads and silently ignores oversized offers. `conn_state_bounded`
covers all connection transitions and includes the closure and snapshot-count bounds; `honest_no_drop` proves that within Conn only
silence expiry can drop, independently of set sizes. Transport
loss and retirement still use the common close-and-purge path.
These are bounds on inbound buffering and persistent per-connection id
state, not a total RSS bound: the shared room index, snapshot contents,
and transient handler allocations are separate. Round/CPU bounds remain
separate work.

## Code

| file | what |
|---|---|
| ops/sync/Fp.lean | keys, ranges, `lbl`, `fp`, `lbl_inj` |
| ops/sync/Round.lean | claims, cutting ranges, `answer`, `exchange` |
| ops/sync/RoundLaws.lean | `exchange_complete` |
| ops/sync/Wire.lean | the three wire kinds and their codec |
| ops/sync/Conn.lean | one connection: room index, rounds, have/want, stream, closure, keepalives |
| ops/sync/ConnLaws.lean | what a connection may take and send |
| engine/core/Held.lean | `Turn` (one write turn) and `Held` (a store as data) |
| engine/wire/Node.lean | the driver; `Hooks` from families; frames and bundles |
| engine/wire/NodeLaws.lean | sealed frames reach the node only opened; the cache law |
| ops/sync/OfferLaws.lean | `have_shown`: what a connection offers |
| engine/wire/Frame.lean | 4-byte length framing on TCP, with proven unframing and bounded buffering |
| engine/wire/Tcp.lean | the TCP runner |
| engine/core/Locality.lean | `spec_local` |
| engine/wire/Pair.lean | two Nodes over a lossy in-memory queue, for tests |
| engine/wire/World.lean | two Nodes on held stores and the frames in flight, as data, with `World.Step` |
| engine/wire/WorldLaws.lean | the entry points run on held stores; `stream_delivers` |
| tests/engine/SyncPair.lean | two-node suites on a real community |
| tests/engine/SyncWorld.lean | the world on a real community, and the stream run as `stream_delivers` says |
| tests/engine/TcpPair.lean | two runners over localhost TCP, with a toy handshake family |

**The driver** (`Node`, generic in its store: `[Monad m] [Store F m]
[Turn F m]`) holds the in-memory room index and the open connections,
and no database. `Turn` is one write turn. On SQLite it is `receive`. On
`Held` (the ops taken in, plus the model's tables) it ingests and then
drains with the proven budget. The driver therefore runs the same on a
device and in a proof's world of nodes as data.

Entry points:
- `Node.onFrame addr bytes now`: every inbound payload. Its first byte
  says what it is:
  - `0x00` and an op's bytes is a bare op, the handshake's, taken
    through `intakeConn` (conn ops only);
  - `0x01` and a sealed frame is opened by the family's `openFrame`
    into (session, bundle); each payload in the bundle goes to that
    session's connection in order.
  Anything else, a frame that does not open, or a frame for a session
  not open here, is ignored.
- `onTick now`, `onWrite ops now`, `onClose addr now`.
- `connect cid addr dialer now`, for the in-memory harness only.

Each entry point returns `Effects`: payloads to send to addresses,
sessions dropped, ids stored and purge roots (for an app's reads).

- Every write goes through `write`: one turn of the ops **not already
  stored**, so a repeat is neither written nor reported again. The
  index grows by what was stored; the stored ids are offered on every
  connection whose peer may see them, each connection's rooms refreshed
  first. Then the family's `react` answers are written, to a fixpoint.
- After every entry point (`finish`):
  - sessions the family lists as established are opened, and ones it
    no longer lists are closed;
  - the family's outbox (bare couriers) is handed out;
  - sends are addressed and sealed. Bare sends go first, so a
    handshake's reply precedes a session's first frame. Each session's
    payloads are bundled, up to `bundle` (48 KiB) a frame, one
    `sealFor` per bundle.
- A session's frames go to the address its last frame arrived from (at
  first, the one its handshake ran on).

**Hooks**, from the Connection family, all in `m`:
- `rooms cid`: which rooms the peer may see (from the session and the
  trust rule).
- `recv`: called on every arrival, a repeat included, after it is
  stored.
- `outbox`: (courier, address, op bytes).
- `shipped`: until purge lands.
- `react`: level-triggered answers.
- `dial`: what to write as time passes.
- `established`: (session, address, dialer).
- `sealFor cid bytes` and `openFrame bytes`: XChaCha20-Poly1305 with
  ad = session, in the family.

**The runner** (`engine/wire/Tcp.lean`, `Runner.start x db floor port
notify`) is the one loop the phone apps and a desktop daemon run.
- It listens, and dials addresses ("a.b.c.d:port") on demand, queueing
  payloads until the dial completes.
- It frames every payload (`Frame.lean`: a 4-byte length, at most
  1 MiB, with proven unframing).
- It hands every inbound payload to `onFrame` with its socket's address.
  An accepted socket's address is its peer's, so replies go back on the
  same socket.
- It closes any socket idle past `idle`, and reports every socket end to the node for key purging.
- The app's writes come in through `Runner.write`; `notify` gets every
  stored id and every purge root, so the app can re-read (a write on the runner's connection
  fires no other connection's triggers).
- One task owns the node and the store; the listener and one reader per
  socket feed it through a channel.
- Stopping closes the event channel, cancels readers, closes sessions and
  releases queued sockets; tests still use `IO.Process.exit` as their harness exit.

## Laws

All on Lean's standard axioms (`mise run check`).

Proven:

- `num_inj`: keys name items.
- `lbl_inj`: equal labels mean equal sets, if `h` has no collision on
  what the two labellings hashed. This is sync's one assumption, of the
  same kind as `Distinct` for op ids.
- `exchange_complete`: one round, the two sides' real `answer`s
  composed, from an honest claim over `r`. Each side is sent exactly
  the ids the other holds in `r` and it lacks, within
  `|X ∩ r| + |Y ∩ r| + 1` answers on any path. Applied to the window
  ranges, this is windowed completeness: after a round, each side holds
  everything the other held in their common window.
- `opening_honest`: how a side opens a round is an honest claim.
- `recv_take`: a session hands the writer only data ops in one of the
  connection's rooms, never a sync wire op, a local op, a conn op, or
  an op of a room the peer may not see.
- `recv_send`, `filed_send`, `tick_send`: a connection sends only sync
  wire ops and ops in one of its rooms. With the notices the node gives
  beside `filed` and `tick` (`filedGive`, `tickGive`): only those, and
  ops of the closure of a notice not given before (`notice_send`), each
  notice once (`notice_sent`, `notice_once`); a have for a room carried
  as a notice gets no reply (`notice_no_holds`).
- `intakeConn_conn`: the bare wire takes conn ops only.
- `have_shown`: every id a connection offers, in a have or an id claim,
  is a stored op of one of its rooms; each step reads only and keeps its
  round snapshots of the index. It rests on the cache law: the room
  index is the index of the ops stored (`Cached`, `cached_items`), and
  every write turn and purge keeps it so (`write_cached`,
  `purge_cached`). Proven of `Conn`'s code on held data; the walk is a
  budgeted recursion (`walkN`), so it can be reasoned about.
- `hold_reply_local`: a have names its room; one for a room the peer
  may not see is ignored, and the reply (which ids to want) reads only
  this side's ops of that room, so two stores that hold the same ops of
  the connection's rooms answer every have alike. With the cache law
  the reply is the room's index (`heldIn_index`).
- `sealed_auth`, `onFrame_sealed`: a sealed frame reaches the node only
  as `openFrame` gives it, and one that fails its AEAD check changes
  nothing and sends nothing.
- `buffer_bounded`, `frames_kept`, `frames_tooBig`: the TCP reader keeps
  less than one maximal frame and its length between reads, and ends
  the connection at a length over `maxFrame`.
- `Op.decode_exact`, `decode_sum`: a decoded op is exactly its bytes; a
  bundle's payloads are together smaller than it.
- `conn_state_bounded`: every reachable connection has known, asked and
  stream-offered at most `maxKnown`, visited plus pending closure ids at
  most `closureCap`, and at most as many snapshots as shown rooms.
  `conn_bounded` retains its original known/asked statement.
- `full_round_stateless`: serving wants with a captured full-range floor
  leaves offered, closed and frontier unchanged.
- `closure_capped`: every prefix of the actual closure walk preserves
  the visited-plus-pending bound.
- `closure_complete_under_cap`: from a fresh windowed closure, every id
  reachable from its seeds is offered, previously streamed, or known
  held, provided a finite stored, shown requirement-closed superset fits
  the cap and the walk has enough fuel. The frontier is then empty.
  `closure_under_cap_runs` supplies a nonempty stored-leaf witness.
- `spec_local` (locality): a decided verdict depends only on the op's
  requirement closure. If a node holds every op the peer's verdict on x
  was reached from, it reaches the same verdict.
- `stream_delivers`, over the two-node world (`World`: two Nodes, each
  on a held store, and the frames in flight as a multiset; `World.Step`
  delivers any frame in flight, ticks, writes or connects, running
  `Node.onFrame`, `onTick`, `onWrite` and `Node.connect` with fixed
  rooms and frames in the clear). Two nodes each hold one session, to
  each other, whose rooms on both sides include room r. A node writes a
  new data op of r, which neither holds and its connection has neither
  offered nor heard the peer holds, and the peer's has not asked for.
  The write sends exactly one frame, the offer; delivered, it is
  answered with exactly one frame, the want; delivered, that is
  answered with frames whose first begins with the op; delivered, the
  peer holds it. The receiver needs one free ask slot; the sender needs a
  positive byte budget and the op in its shown-room index. No spare `known`
  capacity is needed. Each entry point's frames are computed from the code
  (`write_offers`, `hold_wants`, `want_sends`, `op_taken`).
  `stream_delivers_steps`: the exchange is a run of `World.Step`.
  `stream_delivers_runs`: from two empty nodes and two `connect` steps,
  the premises hold, so the law is not vacuous.
- `stream_offered`, over the same world, any number of sessions and
  ops: each op of a write that the store lacked (no other op of the
  write sharing its id) is offered at once on every session whose rooms
  include its room and whose connection has neither offered it nor
  heard that the peer holds it. A frame to the session's address,
  carrying an offer that names it, is in flight. It follows the code's
  loops (`write_offers_all`, `fanout_offers`, `filed_offers`,
  `seal_mem`); `stream_offered_runs` shows it is not vacuous.
- `conn_answers_ids`, the base case of `conn_runs_exchange` below: a
  connection answering a round's claim that lists ids (honestly, the
  claimant's items in the range) sends exactly `exchange`'s offers and
  wants from the round's snapshot, and no claim back. By
  `exchange_ids`, those are the ids the snapshot holds there that the
  claimant lacks, and the reverse.
- `offer_shared`, `offer_stored`: the real filed stream and closure walk
  advertise only stored shared ops; the unused `Engine.offer` is deleted.
- `purges_notified`: the single purge primitive reports every purge root
  in `Effects.purged`; flush and session end carry them to finish.
- `handlers_transition`, `closed_terminal`: every existing connection
  handler respects the session relation; Closed never reopens.
- From earlier: `intake_local`, `stored_local`.

Tested, not yet proven (tests/engine/SyncPair.lean, on a 101-op community with
Ed25519 and SQLite):

- Full sync converges, with the same verdict for every op on both
  sides; completion means equal stored room ops.
- Windowed: a node with a floor ends with exactly its window and the
  requirement closure, and judges every op it holds as its peer does.
- 25% frame loss converges through redials.
- A peer allowed one community never sees another's ops, cannot get
  them by asking, and cannot push them in. Garbage and peers' local ops
  are ignored.
- A new op streams to the peer without another round (proven over the
  world, `stream_delivers`; tests/engine/SyncWorld.lean runs it on a real
  community and checks the premises hold of the live world).

`mise run test:stateless` builds and runs a parameterized 5000-op full
sync over two Nodes, SQLite and memory frames, checking the peak of each
set after transitions. It also checks two signed Community windows: a
closure within 64 slots and one exceeding 16, with a three-visit tick
budget. The former has all verdicts; the latter reports the cut and
checks agreement for decided ops and Missing for incomplete ones.
Boundary checks cover zero capacity, duplicate seeds, cut stickiness,
round reset, delayed wants, and stream-hint eviction. Eight restored
mutations exercise the new bounds, completeness and state-free full
rounds (`tests/engine/stateless_negative.py`). These run in the engine gate.

Earlier negative controls, each failing the suite: windows that ignore the
floor; no closure offers; rooms not checked.

Still to prove:
1. **`conn_runs_exchange`.** Conn's message handling, over any delivery
   order, performs `exchange`. Each round is answered from its
   snapshot, so the claim tree is the same in any order. Stated over
   the world: in any run (`World.Steps`) in which round k of room r,
   opened by the dialer from snapshot Y and first seen by the peer with
   snapshot X, has ended on both sides with none of its frames in
   flight: for each window range w, the ids the peer offered or the
   dialer asked for in it are exactly `(exchange … X Y (opening Y w)).1`,
   and the ids the dialer offered or the peer asked for are exactly its
   `.2`. The base
   case is proven with bounded ask admission (`conn_answers_ids`, a claim
   of ids): offers remain exact, wants take only the admitted subset.
   Completing a large difference now spans rounds. Still to come:
   fingerprint claims, whose answers are claims of their own, and
   delivery in any order. Each side keeps the round's snapshot until
   the round ends, so the claim tree does not depend on the order.
2. **The node chains the steps.** `have_shown` and the cache law are
   proven for each connection step, write turn and purge; that every
   entry point (`onFrame`, `onTick`, `onWrite`) keeps the cache law and
   the snapshots between them is read from the code.
3. **`closure_delivered`.** After a send and its offers are answered,
   the peer holds the op's closure when it fits the cap, given the invariant that `known` is
   a subset of the peer's store. With `spec_local` this gives "every op a
   windowed node holds is judged as its peer judges it", which the tests
   check.
4. **Efficiency.** Repeated offers and sends are allowed when hint
   memory resets or wants retry; at-most-once delivery is not a goal.
   Round-work bounds are still wanted,
   including the counting bound
   `claims ≤ fan · |A Δ B| · ⌈log_fan n⌉` (a mismatched range must
   contain an item of the difference).
5. **Buffering beyond the inbound queue.** The event channel now has
   `queue` slots and blocks producers; socket admission has per-IP and
   total caps. Total RSS, snapshot contents and round CPU work still
   need separate bounds; see the peer-controlled-storage section above.

## Costs

- A round between level nodes: one claim per window range per room,
  each answered by an empty claim list.
- A difference d among n: O(d · fan · log_fan n) claims, and
  `2 + 2⌈log_fan n⌉ − ⌊log_fan leaf⌋` messages per path (Meyer 2023
  §3.2.2).
- A cold side: it holds `leaf` items or fewer, so its opening is its id
  list, and the peer offers everything in one message.
- Fingerprints are computed from each range's items, O(k log k) per
  range. The cached Merkle treap (O(log n) per range, Meyer and Scherer
  Algorithm 2) has the same labels, so it is a drop-in change with no
  wire change. It is the next performance step, proven equal to `lbl`.
  poc-13 measured 3.8× faster catch-up at 500k ops with it; below about
  160k ops, ingest and signature checks dominate.
- The room index is an in-memory sorted list per room, built once at
  boot from the stored ops and grown by every write.

## Caps

- `maxIds` ids per have or want (oversized messages are ignored), and
  at most `maxIds` retried ids per tick.
- `maxKnown` entries in each hint/ask set; forgetting or deferral, never a drop.
- `askTime` bounds ask age; retries do not extend it.
- `wantBytes` encoded response payload bytes plus one whole op.
- `queue` pending inbound events, `maxSocks` sockets and `perAddr` per IP.
- `walk` closure steps per call (the rest continues on the next tick).
- `leaf` and `fan` bound a message's claims.

Grinding a degenerate treap costs the attacker O(n²) hashes and the
victim compute only: rounds, bytes and censorship resistance are
unaffected (Meyer and Scherer §I–II).

## Planned (approved; after the join demo)

- **Sync as an op family (`ops/sync/`, docs/LAYOUT.md).** hello, round
  claims, have and want become ephemeral ops with responders, answered
  from the live store (stores only grow, so `exchange_complete` is
  restated for growing sets). Conn's memory goes away:
  - snapshots: answered from the live store instead;
  - known, offered, asked and closed: content addressing makes repeats
    idempotent ("dedup may only delay a resend, never veto it");
  - peer floor, round counters and liveness: become ops and list reads.
  A "due" standing question opens rounds, as poc-17's `compare.due`
  does.
- **The two-node world.** Built: `World` (two Nodes over `Held`, the
  frames in flight, `now`) and `World.Step`, with `World.Steps` its
  runs (engine/wire/World.lean). Still to come: `Fair` over it, an
  attacker step (holmes-fd, `fd/pair-secrecy`), so lean-net's laws are
  re-proven over the code that runs. The user asked to "induct over
  more". The IO pair should interpret the same step, with a
  model-versus-SQLite differential test.
- **Open, with the user:**
  - rounds from both sides on a cadence, without a dialer bit. Round
    ids must name their initiator, and the cadence should not be every
    tick until the cached treap lands;
  The settled machinery was removed by the user's decision; the screen
  reads the device's own admission.

## Follow-ups

- **The cached treap** with clamped labels (above), and its laws.
- **Purge** (Connection family, holmes-fd): couriers purged when handed
  out, `Node.close` purging a connection's ephemeral ops, and
  `Index.remove` for purged ids. Sync never offers a purged op because
  every offer and send re-reads the store.
- **Message display order (built, 2026-10-28).** A channel displays by
  a counter its devices share: a post claims one more than the highest
  its author holds in the channel (`send`), and the claimed time
  (wall-clock minutes since the Unix epoch, for display) breaks ties,
  then the id (`msg_cmp`, `time_is_display`, `order_total`,
  `send_after`). The counter is claimed, not validated: validating it
  would mean citing earlier messages, which would pull a channel's
  history into every closure. So one post claiming the cap (2^63) or
  more saturates the channel, and every later post claims the cap. A
  saturated message is listed by this device's receipt of it, a local op
  (`received`) numbered in its arrival order, written on sending and on
  every arrival (`Connection.onArrival`). This is the deliberate
  exception to "everyone sees the same state", stated as laws:
  - `display_agrees`: two devices with the same posts order any two
    messages alike unless both are saturated.
  - `arrival_order`: saturated messages show in each device's own
    receipt order (`order_local`: the receipt is the device's own op).
  - `send_after`: a message sorts after everything its author listed in
    the channel when writing it.
  - Two devices that differ: tests/engine/Lifecycle.lean (a theorem
    witness is not built).

  Decided: a receipt is written for saturated messages only; no
  mitigation (authors do not skip removed members' counters); the
  counter and the time each take 8 bytes of the sort key; the counter
  does not feed sync's `ord`, which stays the claimed time, common to
  every timed kind.
- **Wire kinds** as UInt8 (240–242) until the registry names kinds by
  hash.
- **`sync.have` / `sync.want` as a family?** They are transient and never
  stored, so they stay engine wire kinds under the RBSR exception for now.
