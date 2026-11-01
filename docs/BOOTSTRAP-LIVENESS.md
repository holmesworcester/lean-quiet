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

Unqualified fairness is insufficient. An execution can schedule both peers
forever while every useful connection fails, capacity never becomes available,
authorization is repeatedly revoked, or packets arrive only after their round
has expired. A meaningful whole-app theorem needs an eventual stable interval,
usable reachable addresses (currently IPv4 literals), completed I/O, positive
sync budgets and adequate capacity, correct primitive
crypto and collision-compatible retained data. Those assumptions should be
stated about environment behavior, rather than as “bootstrap eventually works.”

Transport capacity includes a per-frame byte bound. `App.textInto` retains the
whole draft and `App.sendNow` only trims it before calling `Community.send`
([App.lean](../App.lean)); that intent and the post validator impose no text-size
limit. A signed draft above 1 MiB can therefore pass the same local validation
as Send while its encrypted frame is rejected by the production TCP reader.
The regression checks this boundary and a small positive control without
publishing the oversized op. For a 32-byte session id and 24-byte nonce, the
tagged frame has `74 + Codec.encode(bundle).size` bytes, so its encoded bundle
must fit **1,048,502 bytes** under `maxFrame = 1,048,576`
([Frame.lean](../engine/wire/Frame.lean), [connection frame](../ops/connection/Frame.lean)).
This is a delivery precondition, not a proven application message-size policy.
