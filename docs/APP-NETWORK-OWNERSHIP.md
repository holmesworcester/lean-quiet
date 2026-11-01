# Network task ownership across App errors

`mise run test:app-network-ownership` builds and runs the actual App,
Runner and SQLite fixture, compiles five causal controls, and restores the
baseline. The engine suite and ready-to-install bootstrap-progress workflow call the same task. Hosted workflow activation remains pending. It requires
the repository toolchains, fonts, Linux user systemd manager and native
SQLite/crypto runtime. Each build runs in a 48 GiB scope without swap. Logs
and SQLite databases remain in `out/app-network-ownership`.

A network boot used to be created by `IO.asTask` and recorded only in the
returned `App.St`. A throwing logger, or a later frame callback failure,
could discard that StateT result while the original Runner still held its
TCP listener. Re-entry then attempted a second boot, and ordinary suspend
could not find or close the original listener. The original actual fixture
completed with eight named failures; the retained artifacts distinguish it
from earlier invalid setup diagnostics.

App now allocates one shared `NetworkOwner` with fixed slots for boot,
installed Runner, stop and replay tasks, plus the original retiring caps.
The frame's existing fields are borrowed views. The real task factory runs
once while registering ownership under the mutex; logging, SQLite work and
joins run outside that mutex. Successful boot adoption retains ownership of
the original Runner. Stop/replay registration atomically claims the current
generation and keeps those exact tasks even when a later callback throws.
A second boot is refused while any original cap or required task remains.
Failed cleanup retains its original caps instead of treating failure as
successful reclamation. Only task-handle storage is fixed; the captured write
journal still scales with accepted pending work. Submissions and network/lifecycle entry points
refresh the borrowed view before deciding where work goes.

The 52-check baseline triggers four real errors: logging and a later actual
frame callback, each both before and after boot adoption. It discards the
failed StateT result, observes the original bound TCP port, recovers that
same Runner, commits a signed operation, and closes the original listener
through App suspend. A fifth case holds the actual Runner closing mutex,
throws after stop/replay registration, checks exact retained task identities,
parks later writes, repeats suspend without duplicate tasks, and verifies
SQLite uniqueness, cleanup and a subsequent restart. Pointer equality is
used only by the test to observe actual Task identity, not by production.
The signed data is synthetic; it is not a captured user community.

The five compiling controls forget the boot, adopted Runner, normal stop,
or replay slot, or allow repeated suspend to replace the stopping generation.
Each must exit 1 with its exact expected assertion list. A compiler error,
crash, unexpected exception or timeout is a failed gate, never a successful
negative control. The restored source must complete all 52 checks again.

This is native regression evidence about resource ownership, not a kernel
proof of the FFI or universal App exception safety. It does not ensure every
one-shot notice survives StateT rollback, make writer admissions exactly-once
across rollback. Reader worker ownership is a separate repair
([APP-READER-OWNERSHIP.md](APP-READER-OWNERSHIP.md)), and a pending normal
stop no longer holds foreground frames ([APP-STOP-UI.md](APP-STOP-UI.md)).
Failed normal cleanup retains its
cap and remains pending. Completion of callbacks, SQLite operations and
native cleanup still needs progress outside this slot protocol. Counts refer
to completed service stages; measured native milliseconds are regression
observations, not an OS scheduling or whole-pipeline latency bound.

On the merged source (origin/main `87df409` plus the stop-UI, frame-time
and Reader ownership repairs), all 1,401 audited laws pass the standard-axiom
audit and the evidence inventory passes (716 entries; the 16 declarations
main leaves pending are unchanged). This suite passes 52
checks, all five controls and restoration. Compatibility on the same source:
failed-runner 77 checks with seven controls, normal suspend 51 with three,
boot admission 13 with two, all restored; lifecycle-node 40/0 with all of
its controls. The lifecycle fixture's late-boot case now stops a runner the
App failed to stop before waiting for replay, so that control fails at its
assertion instead of hanging.
