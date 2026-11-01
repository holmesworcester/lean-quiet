# Bootstrap progress: evidence and boundaries

The checks exercise the running connection handlers with generated users,
signed join requests and messages, native Noise, SQLite and TCP. They also
construct Lean premise certificates before applying the relevant theorems.
They do not use a captured community transcript.

## What the component proofs establish

| Component | Result | Boundary |
|---|---|---|
| [Connection progress](../ops/connection/Progress.lean) | Successful primitive Noise computations produce requests and replies accepted by both actual session validators. A ready approved request produces its answer, ephemeral, established record and courier. | Pointwise crypto equations, wire lengths and concrete store reads are explicit premises. `honest_exchange` derives the equations from `Suite.Good`, supported payloads and successful DH operations. Native examples check the finite equations directly. |
| [Advancing entropy](../ops/connection/ProgressTape.lean) | The actual answer handler consumes its current entropy input, advances the cursor once and preserves its stored data. | Arbitrary entropy tape, explicit store interpreter. The separate `react_contains_answer` law uses `FreshPure` in the deterministic store model; it does not model advancing randomness through all earlier requests. |
| [Dial admission](../engine/wire/DialQueue.lean) | The native runner's bounded waiting queue preserves existing positions, scans destinations in order, respects the global socket bound and admits an eligible head. | Admission still requires available global and per-host slots. Native connects and held sockets must eventually complete or release capacity. The relevant destination workload must fit the pending limit. |
| [Sync rounds](../ops/sync/RoundRun.lean) | `conn_runs_exchange` proves that exact alternating calls to the actual handler terminate and announce every missing ID predicted by the claim exchange. Obsolete room epochs cannot change the connection. | Stable authorized snapshots, honest initial claims, sorted/named items, fingerprint soundness, empty initial ask sets and numeric request capacity. Embedding the isolated round in a timed Node/TCP execution remains separate. |
| [Closure delivery](../ops/sync/ClosureDelivery.lean) | Each persistently stored, authorized queued operation is eventually emitted when positive service capacity recurs, even with unbounded tail arrivals and arbitrary urgent prefixes. Eventual payload delivery gives a common time after which the entire finite requirement closure is held and its verdict agrees with the source. | Discovery must admit each missing closure operation to the sender's queue. The transport must deliver emitted payloads. The source retains authorization and bytes; the receiver retains bytes and has collision-compatible inputs. |
| [Receiver storage](../ops/sync/ClosureStore.lean) | The actual `Node.put`/`Node.write` path accepts shared incoming operations, handles duplicates, retains existing operations and settles validation using its computed turn budget. | This uses the `HeldM` store interpreter. It does not identify native SQLite with that interpreter by assumption or prove the SQLite implementation. |

The queue and closure theorems quantify over infinite sequences of calls to
the actual handlers. Service fairness assumes recurring capacity; closure
separately assumes queue admission and eventual transport. None assumes the
final convergence goal.
The connection theorem is a positive result: its hypotheses do not assume
that the opened or established validators have already succeeded. It checks
the supplied prerequisite facts; reaching those facts in the actual store is
another step in the whole-bootstrap composition.

## Runtime failures found and repaired

Join retries previously selected only the first invite address. A dead first
address could prevent joining through a live later address. Trying every hint
also exposed a transport problem: when four dead addresses shared a host, they
could repeatedly consume its socket quota and the fifth address's send was
discarded. The runner now retains pending destinations in a bounded FIFO and
reserves their available slots before new attempts can overtake them.

A delayed sync response from an old round could rewind the connection's
counter and replace a newer snapshot. Per-room epochs now reject stale and
already-completed rounds and preserve active work for other rooms.

## Run the checks

Run `mise run test:fairness` for the native connection and closure premise
certificates, the infinite fair model witness, the production-node trace and
the real TCP regression suite. The task includes its build and native crypto
setup. `ci/local.sh fairness` invokes the same task; the ordinary engine gate
also invokes it. The [ready PR workflow](../ci/bootstrap-progress.workflow.yml)
configures `test:bootstrap-progress` on Ubuntu: the fairness gate followed by
the sync epoch and claim-tree suites, including mutation controls. It also
configures the witness audit and `host:net-join`'s actual invite/approval/post
UI flow, installs native/font prerequisites and retains artifacts.

**PR automation is not active:** GitHub rejected publishing the workflow
because the configured token lacks `workflow` scope; SSH access was unavailable.
With a suitably scoped credential, copy the reviewed configuration to
`.github/workflows/bootstrap-progress.yml` and commit it. The named gates run
locally today; a hosted run is still needed to validate clean-runner setup.
`mise run check` audits the Lean laws for nonstandard axioms.

The TCP suite uses Linux loopback sockets, two production runners, separate
SQLite databases and controlled relays. It covers delayed approval, sustained
local writes, backpressure, disconnect/reconnect and unreachable invite hints.
Mutation controls must detect reintroduced starvation and hint/slot failures.
Native panic, timeout or a failed assertion fails the suite. Build and run logs
remain in `out/fairness`, `out/join-fair` and `out/ci`.

## What still needs a full-app theorem

These results do not yet prove convergence of **every suitably fair execution
of the whole application**. The production interpreter has a successful finite
trace and an infinite fair continuation. Component proofs establish more than
that witness, but their composition still needs to be proved:

1. Project the actual runner's sessions, retries, room changes and transport
   events into the handler sequences used by the progress theorems.
2. Establish discovery and queue admission for every missing dependency across
   capped windows, completed rounds and reconnects.
3. Establish the repeated ordinary service opportunities and retained source
   authorization required by closure delivery.
4. Connect reaction writes, validation and session following through the entire
   bootstrap, and state the store/transport refinement boundary explicitly.

The earlier round/closure components have stronger premises about stable
sessions, room/capacity and delivery. Those are **not accepted environment
assumptions for the strengthened goal**: the running app must supply its own
fair service and persistent retries. A durable per-authenticated-peer catalog
cursor now retries actual authorized op bytes across changing session IDs,
without relying on delivery of a round opening, have or want. The cursor law
allows continuing inserts and zero-room stalls; deriving its recurring output
reservation from the complete native runner is still open. Revoked/private
data, unsupported bytes and missing prerequisites require explicit domain
boundaries, not an assumption that bootstrap eventually succeeds.

Transport capacity includes a per-frame byte bound. The low-level send intent
and validator still accept a signed post above 1 MiB, but `App.writeAll` now
refuses it before optimistic display or submission. Send retains the draft
and reports the reason. With a 32-byte session id and 24-byte nonce, a tagged
frame has `74 + Codec.encode(bundle).size` bytes; the admission check requires
each op's singleton bundle to fit **1,048,502 bytes** under the 1 MiB limit.
It also refuses new batches exceeding 8,192 pending ops or 128 MiB of pending
encoded data. `host:write-admission` runs actual Send against SQLite, checks
refusal and recovery, and rejects three mutations of the proven bounds.
These checks cover that app entrypoint, not historical/imported data or all
other submission paths.

The strengthened, no-quiescence execution target and the unresolved whole-app
resource/UI obligations are tracked in [EXECUTION-PROGRESS.md](EXECUTION-PROGRESS.md).
