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
all of the claimant's ids in it. `answer` (Engine/Sync/Round.lean):
- a matching fingerprint settles the range;
- if this side holds `leaf` (128) items or fewer there, it answers with
  its ids;
- otherwise it cuts the range into up to `fan` (16) pieces of nearly
  equal count and claims each by its fingerprint;
- a claim of ids is answered with what this side holds there that the
  claimant lacks (`hold`) and what it lacks (`want`).

Each side answers a round's claims from a snapshot of the room taken
when it first saw the round. A message with no claims ends the round.

**Have and want.** `hold` goes out as `sync.have`. The peer wants what it
lacks (`sync.want`), and wanted ops are sent as their own bytes. A want
for an id outside the connection's rooms, a local or conn op, or an
unknown id, is ignored silently.

**Stream.** Between rounds, each op newly stored is offered
(`sync.have`) on every connection whose peer may see it and is not known
to hold it. The stream is only ever safe (laws below). Liveness comes
from rounds.

**Closure.** With each op sent goes an offer of its requirement closure:
the ids the peer is not known to hold. The walk stops at ops whose
closure this connection already offered and that are Valid here, since
a Valid op's closure is complete and can never grow. It visits at most
`walk` ops per call and continues on the next tick, so nothing is
capped silently.

**Patience.** While a side waits (for the peer's hello, a round's
answer, or ops it wanted after the peer said it holds them), a peer
silent for `patience` ms drops the connection. The next connection's
round finds what is still missing. Silence, not age, is the trigger, so
a large sync that is making progress is never dropped.

**Status.** `settled room` once per room per connection, when its first
round has ended and nothing wanted is outstanding. The Connection
family writes it as a local op, so it can't grow the log per message.

## Code

| file | what |
|---|---|
| Engine/Sync/Fp.lean | keys, ranges, `lbl`, `fp`, `lbl_inj` |
| Engine/Sync/Round.lean | claims, cutting ranges, `answer`, `exchange` |
| Engine/Sync/RoundLaws.lean | `exchange_complete` |
| Engine/Sync/Wire.lean | the three wire kinds and their codec |
| Engine/Sync/Conn.lean | one connection: room index, rounds, have/want, stream, closure, patience |
| Engine/Sync/ConnLaws.lean | what a connection may take and send |
| Engine/Sync/Held.lean | `Turn` (one write turn) and `Held` (a store as data) |
| Engine/Sync/Node.lean | the driver; `Hooks` from families; frames and bundles |
| Engine/Sync/NodeLaws.lean | sealed frames reach the node only opened; the cache law |
| Engine/Sync/OfferLaws.lean | `have_shown`: what a connection offers |
| Engine/Sync/Frame.lean | 4-byte length framing on TCP, with proven unframing and bounded buffering |
| Engine/Sync/Tcp.lean | the TCP runner |
| Engine/Sync/Locality.lean | `spec_local` |
| Engine/Sync/Pair.lean | two Nodes over a lossy in-memory queue, for tests |
| Tests/SyncPair.lean | two-node suites on a real community |
| Tests/TcpPair.lean | two runners over localhost TCP, with a toy handshake family |

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
- `onTick now`, `onWrite ops now`.
- `connect cid addr dialer now`, for the in-memory harness only.

Each entry point returns `Effects`: payloads to send to addresses,
sessions dropped, and ids stored (for an app's reads).

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
- `settled`: what a room's first settle writes.
- `recv`: called on every arrival, a repeat included, after it is
  stored.
- `outbox`: (courier, address, op bytes).
- `shipped`: until purge lands.
- `react`: level-triggered answers.
- `dial`: what to write as time passes.
- `established`: (session, address, dialer).
- `sealFor cid bytes` and `openFrame bytes`: XChaCha20-Poly1305 with
  ad = session, in the family.

**The runner** (`Engine/Sync/Tcp.lean`, `Runner.start x db floor port
notify`) is the one loop the phone apps and a desktop daemon run.
- It listens, and dials addresses ("a.b.c.d:port") on demand, queueing
  payloads until the dial completes.
- It frames every payload (`Frame.lean`: a 4-byte length, at most
  1 MiB, with proven unframing).
- It hands every inbound payload to `onFrame` with its socket's address.
  An accepted socket's address is its peer's, so replies go back on the
  same socket.
- It closes any socket idle past `idle`.
- The app's writes come in through `Runner.write`; `notify` gets every
  stored id, so the app can re-read (a write on the runner's connection
  fires no other connection's triggers).
- One task owns the node and the store; the listener and one reader per
  socket feed it through a channel.
- A test that runs it must call `IO.Process.exit`, because Lean waits
  at exit for the runner's never-ending tasks.

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
  wire ops and ops in one of its rooms.
- `intakeConn_conn`: the bare wire takes conn ops only.
- `have_shown`: every id a connection offers, in a have or an id claim,
  is a stored op of one of its rooms; each step reads only and keeps its
  round snapshots of the index. It rests on the cache law: the room
  index is the index of the ops stored (`Cached`, `cached_items`), and
  every write turn and purge keeps it so (`write_cached`,
  `purge_cached`). Proven of `Conn`'s code on held data; the walk is a
  budgeted recursion (`walkN`), so it can be reasoned about.
- `sealed_auth`, `onFrame_sealed`: a sealed frame reaches the node only
  as `openFrame` gives it, and one that fails its AEAD check changes
  nothing and sends nothing.
- `buffer_bounded`, `frames_kept`, `frames_tooBig`: the TCP reader keeps
  less than one maximal frame and its length between reads, and ends
  the connection at a length over `maxFrame`.
- `Op.decode_exact`, `decode_sum`: a decoded op is exactly its bytes; a
  bundle's payloads are together smaller than it.
- `spec_local` (locality): a decided verdict depends only on the op's
  requirement closure. If a node holds every op the peer's verdict on x
  was reached from, it reaches the same verdict.
- From earlier: `intake_local`, `offer_shared`, `stored_local`.

Tested, not yet proven (Tests/SyncPair.lean, on a 101-op community with
Ed25519 and SQLite):

- Full sync converges, with the same verdict for every op on both
  sides, and both report the room settled.
- Windowed: a node with a floor ends with exactly its window and the
  requirement closure, and judges every op it holds as its peer does.
- 25% frame loss converges through redials.
- A peer allowed one community never sees another's ops, cannot get
  them by asking, and cannot push them in. Garbage and peers' local ops
  are ignored.
- A new op streams to the peer without another round.

Negative controls, each failing the suite: windows that ignore the
floor; no closure offers; rooms not checked.

Still to prove:
1. **`conn_runs_exchange`.** Conn's message handling, over any delivery
   order, performs `exchange`. Each round is answered from its
   snapshot, so the claim tree is the same in any order.
2. **The node chains the steps.** `have_shown` and the cache law are
   proven for each connection step, write turn and purge; that every
   entry point (`onFrame`, `onTick`, `onWrite`) keeps the cache law and
   the snapshots between them is read from the code.
3. **`closure_delivered`.** After a send and its offers are answered,
   the peer holds the op's closure, given the invariant that `known` is
   a subset of the peer's store. With `spec_local` this gives "every op a
   windowed node holds is judged as its peer judges it", which the tests
   check.
4. **Efficiency.** Each op's bytes are sent at most once per
   connection; each id is offered at most once; each Valid op is walked
   at most once; and the counting bound
   `claims ≤ fan · |A Δ B| · ⌈log_fan n⌉` (a mismatched range must
   contain an item of the difference).

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

- `maxIds` ids per have or want (a want for more is ignored).
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
  - peer floor, round counters and patience: become ops and list reads.
  A "due" standing question opens rounds, as poc-17's `compare.due`
  does.
- **The two-node world.** `World := { nodes over Held, wire, now }` and
  `step`, with `Reachable`/`Run`/`Fair` defined over it, so lean-net's
  laws are re-proven over the code that runs (holmes-fd). The user
  asked to "induct over more". The IO pair interprets the same step,
  with a model-versus-SQLite differential test.
- **Open, with the user:**
  - rounds from both sides on a cadence, without a dialer bit. Round
    ids must name their initiator, and the cadence should not be every
    tick until the cached treap lands;
  - whether to keep `settled`, or have the screen read the device's own
    admission instead.

## Follow-ups

- **The cached treap** with clamped labels (above), and its laws.
- **Purge** (Connection family, holmes-fd): couriers purged when handed
  out, `Node.close` purging a connection's ephemeral ops, and
  `Index.remove` for purged ids. Sync never offers a purged op because
  every offer and send re-reads the store.
- **Message display order (follow-up; not built).** Display a channel by
  a channel-wide counter shared across devices. A new message's counter
  is higher than any it has seen in the channel, and the timestamp
  breaks ties. If the counter saturates, fall back to "received at",
  recorded as a local op. This is a deliberate exception to "everyone
  sees the same state", stated as laws:
  - `display_agrees`: two devices with the same shared ops order any
    two messages alike unless both are saturated.
  - `display_local`: saturated messages show in each device's own
    receipt order.
  - `exception_real`: a witness of two devices that differ, and only
    there.
  - `reply_below`: a message shows below what its author held when
    writing it, unless saturated.

  The counter is claimed, not validated: validating it would mean citing
  earlier messages, which would pull a channel's history into every
  closure. So one message at the top value saturates the channel; the
  cheapest mitigation is that authors take the max over messages by
  members who have not been removed. Open choices:
  - whether received-at is recorded for every message or only saturated
    ones;
  - whether to apply that mitigation;
  - the counter's width (UInt64).
- **Wire kinds** as UInt8 (240–242) until the registry names kinds by
  hash.
- **`sync.have` / `sync.want` as a family?** They are transient and never
  stored, so they stay engine wire kinds under the RBSR exception for now.
