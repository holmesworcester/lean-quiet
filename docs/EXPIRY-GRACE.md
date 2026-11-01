# Admitted input gets a bounded opportunity before silence expiry

Using synthetic identities and posts, an actual native diagnostic reproduced
a loss window with honest signed
memberships, production Connection hooks, Noise/AEAD, SQLite, TCP readers and
writers, and the real `Loop.turn`/`RunState.loopBackend`. A decryptable post was
already in the receiver's mailbox. After a finite pause longer than the
configured silence timeout, a local-preferred turn processed a local write
and then expired the session, erased its key and canceled that mailbox. The
peer-first control processed the post and refreshed liveness before expiry.
This did not involve moving bytes from a closed socket to a replacement one.

The runtime now gives an already-admitted source one finite opportunity
before ordinary session-silence or socket-idle expiry. The actual selector
still gives local work three preferred slots per four polls. No extra network
drain runs ahead of local work. The budget is `4 * (maxSocks + 1)`, the
existing prioritized ingress source bound: 260 selections for the default
64 socket slots, 20 in the native regression. Each subsequent primary
selection consumes one unit. Timer ticks and new pending bytes do not refill
it. An empty mailbox does not delay expiry.

A session's episode is tied to its actual authenticated `Conn.heard` value.
Once exhausted, repeated junk cannot rearm it. Only the existing successful
session receive path can advance that value. Socket idle uses its separate
handled-input timestamp, as before; unauthenticated traffic cannot thereby
renew the authenticated session budget. Connection/source churn leaves other
entries' budgets and the selector cursor intact. Entries are removed with
the corresponding live connection or socket.

Before deferring timed work, Node refreshes authorization and notices from the
actual store. Fresh authenticated notices bypass grace. Dial/reaction,
follow/retirement and the final close-and-purge path still run. Explicit socket
failure, authenticated retirement/removal, shutdown, protected-control refusal
and native stalled-send cancellation do not consult grace. This change does
not retain session keys across transport failure or change key replacement.

Eleven kernel laws cover the exact executable grace core: same-generation
checks cannot reset a budget, consumption decreases and saturates, exhausted
or empty-source checks cannot delay expiry, and the existing source bound
provides a service-or-explicit-retirement opportunity before exhaustion.
Nonempty witnesses have continuing local and peer arrivals plus unrelated
source retirement/reuse. The native wrapper's correspondence to those states
is tested, not a complete OS/SQLite refinement theorem.

`mise run test:expiry-grace` builds the laws, witnesses and native executable,
checks standard Lean axioms, and runs 29 assertions. The native cases require
both session-silence and socket-idle progress under continuing local writes;
real unauthorized Noise requests must expire after the finite budget; an
actual founder removal must erase keys despite active grace and drain its
signed notice to an admitted receiver. A notification barrier lets the actual
reader refill its mailbox for the junk test; no fake ingress events, session
tables or connection hooks are substituted. The restored suite must pass after
two compiling controls: no grace, and pending junk resetting the budget.

These tests use fixed five-second silence settings and a 5.1-second finite
pause. These are diagnostic settings, not latency guarantees. The original
one-second/1.1-second reproduction is retained in the audit artifacts. The
removal receiver explicitly waits for native output admission before it
resumes: grace does not promise delivery of a notice still in flight.

The named task requires the pinned native Lean/Rust/crypto toolchains, Linux
localhost TCP, SQLite, Python and a user systemd manager. Every Lean/Lake build
uses MemoryMax=48G and MemorySwapMax=0. Fresh databases and all baseline,
control and restoration logs remain under `out/expiry-grace`. The engine
aggregate and bootstrap CI template invoke the same named task; the template
must be activated as a workflow before it supplies CI coverage.

Still open: arbitrary-execution convergence under raw fair-loss transport;
ordinary close/reconnect and acknowledged key replacement; completion of
native/store calls; whole-app memory/work bounds; and fixed wall-clock or
complete commit-to-display latency. Fresh encryption nonces require a
sender-side logical-message projection for fair loss. Defining delivery as
already authenticated operation acceptance would hide the remaining protocol
obligation in the environment assumption.
