# Network boot under continuing local App writes

`mise run test:app-boot-admission` builds the real App/Runner/Writer fixture,
runs its 13 checks, compiles two causal controls, and restores the baseline.
The ready CI workflow template invokes the same named task; hosted activation
is pending. It needs the repository toolchains, fonts,
SQLite/native runtime and a Linux user systemd manager; builds use 48 GiB
scopes without swap. Logs and databases remain in `out/app-boot-admission`.

Previously, `App.netStep` returned while the Writer was busy, before it
installed `netBoot`. Later `App.submit` calls therefore continued adding
Writer jobs. Continuing local arrivals could prevent any boot task from
being installed even while the Writer completed jobs and UI stages ran.

The completed network service now retains a dedicated boot task before
waiting. That task waits for earlier Writer work before opening the node's
store. Later App submissions see `netBoot` and park in acceptance order;
they no longer extend the Writer backlog that this task awaits. Existing
normal-stop and journal-replay guards still prevent another boot from
bypassing either retained task. This is about submissions through App,
not arbitrary independent producers calling Writer.submit directly.

The fixture accepts a synthetic signed operation into the actual paused
Writer, invokes the network service, and sends twelve more signed operations
through actual App submission and frame functions. It checks the boot handle,
parked order, finite earlier backlog, continuing frame publication and durable
checkpoint bytes. After releasing the Writer it checks real Runner startup,
SQLite validity and catalog order/uniqueness, journal acknowledgement and
normal cleanup. The original implementation failed four checks while still
committing all operations once local arrivals stopped.

One compiling control restores the caller's busy guard and reproduces that
failure. The other removes the task's wait and must expose a premature node
and later operations overtaking the paused first write. Both require their
named assertion failures with exit 1; crashes, build failures and timeouts
are gate failures. The setup briefly observes the actual boot task while
the real Writer remains paused; it does not replace startup with a model.

The fixed boundary is one completed eligible App network-service invocation
to retained boot ownership. Eventual earlier writes and node startup still
require the Writer's storage operations and native task scheduling to make
progress. Native milliseconds are regression observations, not a global UI
or network latency theorem. This fixture does not prove native implementations
or make App StateT task registration exception-safe: task creation followed
by a throwing logger or outer state rollback remains a separate ownership
boundary. No existing write-before-node-snapshot ordering was removed.

The first combined-source control run caught premature startup but inspected
SQLite before the separate Runner had completed a write turn. It is retained
as a failed test-driver run, not a successful mutation rejection. The fixture
now observes the prematurely started Runner's actual completed-write counter
before checking overtaking; absence of service is a fixture error. All 13
assertions, both control requirements and original outcome deadlines remain.
