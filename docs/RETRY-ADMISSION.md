# Retry admission across sessions sharing a socket

The running Node now keeps a retry order separately from ordinary connection
work. Live waiters keep their place, new sessions join the tail, and only
sessions that actually produce an admitted retry offer move to the tail.
Busy reservations and empty/ineligible sweep steps do not rotate waiters.
The UI-first selector and ordinary connection traversal retain their policy.
Direct, nondeferred interpreters still call the original tick body.

## Demonstrated failure and repair

The original real Runner/SQLite/TCP fixture opened three authorized sessions
on one socket and repeatedly completed actual native writes. With its
one-row catalog it delivered `[60, 60, 0]` payloads over 121 completed ticks.
Moving the third session to the front changed the counts to `[60, 0, 60]`.
The failure was position-dependent starvation, despite successful sends and
continuing loop steps. The original binaries, outputs and source hashes are
retained in the development evidence archive.

A completed cursor reaches its sweep boundary on the following tick. The old
fixed traversal then lets the other leading session claim the reservation;
the first restarts before the third can claim it. Reordering after actual
offers breaks that cycle. Both original orders now deliver `[40, 40, 40]`
through the real socket over 121 ticks. These are regression observations,
not universal native timing bounds.

`Node.sweepAll` calls `RetryOrder.reconcile`, the singleton `scan` admission
step and `offered` rotation. Candidate payloads are consumed immediately;
it does not retain one full frame per waiting session. At most one candidate
claims each address in a pass. A refused deferred candidate does not advance
the durable cursor; the nonpersistent fallback restores that candidate's
previous cursor as well. Skipped missing/unauthorized rows may still advance.
The existing reservation/native-batch bounds and sealing authorization
statements are unchanged. The post-reconcile retry order has one entry per live session
when the live and prior lists are unique; this is not a global session cap.

## Kernel result and its boundary

`RetryOrder.offered_or_retired` proves service or explicit retirement within
`p + 1` **pending-eligible, initially vacant reservation opportunities**,
where `p` counts every earlier queue entry. Arbitrary subsequent arrivals,
removals, eligibility changes and other socket routes are permitted. A busy
tick is not such an opportunity. No selector-fairness or posting-quiescence
assumption occurs in this rank theorem.

The trace is observed at the post-reconcile selection boundary. Its next
queue is the previous scan's actual offer rotation, reconciled against the
live sessions seen at the following pass. The proof names the same streaming
`scan` that the runtime calls for each candidate; `scan_append` composes
these singleton calls. The required uniqueness and transition premises are
explicit. `waiting_rank` shows that a waiting target's rank never increases,
and decreases on each eligible vacancy. No unserved waiter moves behind a
later arrival just because a busy tick completed.

`tests/vacuity/RetryOrder.lean` constructs a nonempty infinite core execution.
It continually adds a new session, retires the previous newcomer, keeps three
old sessions live, and runs the executable scan/reconciliation functions.
Its first three offers are the three old sessions; its opportunity count is
unbounded. It instantiates the general rank theorem without a quiescence
premise. A second closed instantiation uses the running `Engine.Id` and
`ByteArray` address types, discharging lawful equality with the existing
`Engine.lawfulBEqByteArray` theorem. These are core execution witnesses, not
a complete application run.

Still open: derive candidate eligibility, queue uniqueness and recurring
vacancies along every suitable full Node/Sweep/native execution, and compose
admission with actual writer completion, durable cursor acknowledgment and
semantic fair-loss delivery. The rank theorem does not assume those app
obligations have already happened, and does not prove them. In particular,
preparing or admitting an offer is not a wire send; native completion and
key/session lifetime remain separate stages.

## Security reachability and realistic regression

The focused scheduling fixture uses the actual Node, SQLite, Runner and TCP
writer, with explicit fixed authorization hooks and plain sealing. Its
receivers ingest the signed root into separate SQLite connections and check
valid derived facts after the receiving task stops.

The companion `RetryReachability` fixture constructs real signed invitations,
requests, approvals and admissions for three different peers, and real Noise
request/reply/established operations. The production validator, `sessions`,
`rooms`, `retryKey` and frame-opening hooks run against SQLite. Authenticated
frames then cause the actual `Node.onFrame` to learn one shared transport
address for all three sessions; production `follow` preserves those routes.
Each retry identity is the distinct authenticated peer key. This demonstrates
that multiplexing is reachable without inventing keys or bypassing room
checks. It does not assert that the focused one-row catalog is a complete
production handshake history or prove the fairness of every such history.

`retryKey` is peer-scoped. Production `roomsV` authorizes all shared rooms for
that peer, and `openSessions` keeps one session per peer. The fixture does
not create conflicting community-specific cursors for one remote identity.

## Reproducible gate

Run `mise run test:retry-admission`. It builds crypto and the actual native
fixture, checks the infinite kernel witness, then runs baseline, five
compiling runtime controls, one unchanged-proof control, and restoration.
Local engine CI and the bootstrap-progress task invoke that same task. The
prepared bootstrap workflow retains `out/retry-admission`; enabling the
hosted workflow remains subject to the repository's existing workflow setup.

Prerequisites are the pinned Lean toolchain, Rust/native C toolchain,
SQLite sources, Linux loopback sockets and a working systemd user manager.
Every Lean/Lake build runs with `MemoryMax=48G` and `MemorySwapMax=0`.
Logs stay in `out/retry-admission`. A missing mutation anchor, compile error,
timeout, signal, panic or unrelated failed assertion is a gate failure,
never a successful negative control.

The runtime controls restore fixed traversal, let newcomers jump the queue,
rotate on busy ticks, advance refused fallback cursors, and overbook an
address. The proof control removes offer rotation and must fail the unchanged
`RetryOrderLaws` module. Existing reservation and expiry-grace suites retain
their original assertions and deadlines.

## Combined-source integration

After primary commit `215da26`, the retry and admitted-input close repairs
pass the full 1,330-law standard-axiom audit. The named retry gate passes all
29 checks, rejects all five compiling runtime controls and its kernel control,
and passes after restoration. Both native initial orders deliver `[40,40,40]`;
observed completion is 121–122 runner ticks. These are native observations,
not a fixed tick theorem. The close and original expiry gates also pass with
their controls. Exact logs are under `out/ci/transport-integrated-*.log`.
The nonempty kernel witnesses pass the complete evidence dependency audit.

The subsequent merge with `4bac90d` preserves the store-backed purge bridge,
session-key erasure fixes and switcher backdrop changes. The combined source
passes all 1,342 audited laws, all 689 witness dependency/axiom checks and
runtime certificates, and the retry, close and expiry gates with every control
and restoration again. Logs: `out/ci/transport-purge-merge-*.log`. A completed
close is the erasure boundary; admitted-input grace and native IO completion
do not establish a universal 90-second wall-clock deadline.
