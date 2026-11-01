# Session and retry-order uniqueness

The actual `Node.boot` starts with unique connection IDs and retry-order
entries. Every actual `Node.step` handler preserves both properties: writes,
frames, timers and transport closes. `Node.open` removes an existing entry
before replacing it, fanout preserves the ID sequence, and applying or serving
a connection does not change its ID. The reserved sweep uses the existing
`RetryOrder.reconcile_nodup` and `offered_nodup` laws.

No runtime code changed for this milestone. The previous uniqueness premise
is now derived as an app invariant rather than left as a requirement on peers
or hook output. Duplicate established-session rows are allowed as inputs.
The invariant does not assert that the retry queue contains only live sessions
between reconciliation points, nor does it bound the number of sessions.

## Exact theorem boundary

`Engine.Sync.NodeUnique.Ensures action P` means the **actual monadic action** is
exactly `Subtype.val <$> checked` for an action returning values with proofs
of `P`. Thus the proof follows the running handler's branches and loops; it
is not a parallel state-machine implementation. The generic theorem supports
arbitrary effectful hooks and backing stores. The SDK IO monad laws are proved
from its pinned bind/pure definitions; they are not an added assumption.
`sql_step_valid` specializes to the actual `SqlM` action and database used by
TCP. It is a returned-value safety statement. Exceptions, nontermination,
foreign code integrity and native completion are not turned into success.

The application proof reuses `Connection.Execution.World`, `step`, `trace`
and `Run`. Every finite prefix and every position of an infinite run from
boot has unique IDs, without fairness, quiescence or cryptographic premises.
That World uses production hooks and an explicit Held store/entropy tape;
it is not silently identified with the concurrent native runner.

This closes the connection/retry uniqueness obligation. Still open are the
full correspondence between Node's streaming sweeps and the rank theorem's
successive scans, recurring pending/eligible vacancies, native writer
completion and the raw-wire-to-semantic fair-loss/key-lifetime bridge.
Neither uniqueness nor the rank bound proves per-operation delivery alone.

## Witnesses and controls

`tests/vacuity/NodeUnique.lean` uses synthetic Unit-family labels for kernel
computation. It opens and replaces a nonempty session, reconciles a singleton
retry queue, and proves an infinite actual-handler execution stays nonempty
and unique while hostile empty frames keep arriving. These are bookkeeping
witnesses, not cryptographic certificates. Separate instances apply the actual
SQLite action and existing production-hook World/Run theorems.

`mise run test:node-uniqueness` builds the proofs and actual native fixture,
checks 11 principal/helper laws against the standard-axiom allowlist, and runs
real signed invitation/approval, Noise, TCP and SQLite setup. The fixture checks
an actual signed write, every observed handler prefix, duplicated real
established-hook rows, actual repeated open, repeated sweep and transport close.
The repeat-open case calls that production handler directly on the authenticated
state; it is not claimed to be another remotely requested handshake.

Two controls must compile: duplicate an actual newly followed session and
insert duplicated IDs into the retry-order input. Each must fail its designated
native assertion, and the unchanged uniqueness proof must also fail. A third
kernel control removes open's replacement; the legacy WorldLaws already reject
that change on the native import path, so its compile failure is not counted
as a native runtime control. The restored source must pass again. Existing
fixture bodies and imports remain unchanged.

Prerequisites: pinned Lean, Rust/C toolchains, SQLite sources, Linux loopback
sockets, Mise and a working systemd user manager. Every Lean/Lake process runs
with `MemoryMax=48G` and `MemorySwapMax=0`. Engine CI and the prepared bootstrap
workflow invoke the same named task. Hosted workflow activation retains its
existing repository prerequisite; preparing it is not a remote CI run.
Logs and per-run SQLite databases remain under `out/node-uniqueness`, outside
mutation snapshots. Compile errors, timeouts and unrelated failures are gate
failures, never passing runtime controls.

The combined primary source, including native job ownership, passes all 1,355
audited laws. The named uniqueness task passes 10 native checks, both runtime
controls, three kernel controls and restoration. All 707 linked evidence entries
pass the dependency/axiom audit and registered runtime certificates, with eleven
inventory tests. These checks do not replace full app/platform validation or the
separate retained-session policy follow-up.
