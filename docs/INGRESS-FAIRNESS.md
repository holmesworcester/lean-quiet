# Bounded peer ingress while local work keeps priority

The running TCP reader now admits frames to one fixed mailbox per retained
socket. The event loop polls those mailboxes through `Ingress.State.poll`;
slot zero holds runner control. A peer cannot overwrite an admitted frame or
move the consumer's cursor by reconnecting. Admission uses a bounded offer
with explicit retirement/shutdown cancellation instead of an SDK channel
producer promise. The SDK may wake a producer without reserving the freed
slot, and closing its channel does not release existing producer waiters.

The outer `Inbox.Priority.next` policy is unchanged: three local-preferred
phases, then one network-preferred phase, with immediate fallback when the
preferred input is empty. Per-peer rotation happens inside the network input.
A local write therefore never waits behind an entire round of peers.

## Kernel-checked claims and their exact boundaries

`IngressLaws.source_within` serves an occupied mailbox within `maxSocks + 1`
network polls. `IngressPriorityLaws.source_within` composes the actual poll
with the actual outer selector: service occurs within `4 * (maxSocks + 1)`
completed loop turns, even with arbitrary further peer and local arrivals.
`IngressPriorityLaws.write_within` retains the local bound of `2 * (p + 1)`
turns for a queued write with `p` earlier writes. `IngressChurnLaws` permits
arbitrary other-peer retirement and slot reuse: the admitted target is served
or its own incarnation is explicitly retired within the same bound.
The cursor, cancellation and offer functions in these proofs are called by
the native `Hub`; these are proofs of its executable selection core.

There is no selector-fairness premise. A ready value means one already
admitted to its mailbox or local queue. Bounds count completed turns, not
wall-clock time, producer admission, SQLite completion or native callbacks.
The peer scan has fixed fuel equal to the mailbox count. The registry has a
fixed number of slots; each dedicated reader additionally retains at most one
frame while waiting for its mailbox. This does not bound all application
memory, all payload construction or all thread lifetimes.

## Runtime checks and controls

Run `mise run test:ingress` on Linux/POSIX with localhost TCP and the repository's
Lean, C and Rust toolchains. The task builds its prerequisites and proofs,
runs the real TCP/SQLite runner, then builds eight isolated mutations. The
engine suite and bootstrap-progress CI invoke the same named task. Logs,
databases and mutation build output remain in `out/ingress`. Every Lean/Lake
build is limited to 48 GB with swap disabled.

The native suite has 65 checks. Four TCP peers fill their actual mailboxes
behind an actual runner notification barrier; three continue flooding while
an honest signed marker and local writes remain ready. The marker must be
applied within 20 turns and the local head committed/readable within two
turns and 500 ms. Observed baseline: one local turn, 14–15 marker turns;
process descriptors return from 13 to 13. Additional cases exercise quota
reuse before due-tick reaping, stale-source rejection, retirement/shutdown of
backpressured TCP readers, and cancellation of public write/control waits on
stop, closed queues or actual runner failure.

All eight controls compiled and failed their named runtime assertion:
resetting the cursor, reusing an occupied source, ignoring peer cancellation,
overwriting an owed mailbox, restoring SDK write waiting, ignoring control
admission cancellation, ignoring unanswered-reply cancellation, and ignoring
runner failure. Both four-case diagnostic runs restored the full 65-check
suite successfully. Signal termination, panic and unrelated runner failure do
not count as successful controls.

The first fixture incorrectly shared one SQLite connection between the
runner and observer threads. A preserved GDB trace identified concurrent
`le_sql_query` calls and a crash in `sqlite3DbMallocRawNN`; the pinned SQLite
uses `THREADSAFE=2`. The fixture now uses a separate on-disk observer
connection through normal `Db.openAt`, matching the application. Four
consecutive full baselines and both mutation gates passed after this causal
repair. No production SQLite threading policy or latency limit was changed.

## Still open

The bounded selector does not prove fair admission among producers competing
for the control channel or local-write queue. Public waits observe stop,
closure and runner failure; a live overloaded producer may still be overtaken.
Native OS scheduling, connect/teardown completion, failed capability capture,
and Windows cancellation need separate treatment. The [native-lifetime follow-up](NATIVE-LIFETIMES.md) now retains a socket lease
until its original reader task finishes. Final OS-thread teardown and native
callback scheduling remain outside the selector proof. Whole
operation tables, engine drain/index work, caches, operation sizes and some
counters remain unbounded. Full-app UI paint latency and per-operation
convergence for every fair-lossy execution do not follow from these selector
claims; durable session/retry delivery obligations remain separate.
