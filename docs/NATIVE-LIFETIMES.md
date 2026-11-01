# Native socket lifetime regressions

`mise run test:native-lifetimes` builds and runs the real TCP runner and its
socket cleanup helpers. The gate requires Linux x86-64, localhost TCP,
GDB with permission to trace its own child, the pinned Lean 4.34.0 SDK,
C/Rust toolchains and a working systemd user manager. Every Lean/Lake build
runs in a scope with `MemoryMax=48G` and `MemorySwapMax=0`. The named task is
included in the local bootstrap-progress gate and its checked-in CI workflow
template. That template must be installed under `.github/workflows` before
GitHub runs it. Logs are retained under `out/native-lifetime`; a prerequisite,
build, debugger or timeout failure fails the gate.

The 24 runtime assertions and two forced SDK interleavings cover related repairs:

- Outgoing connects bind before capturing their POSIX abort capability.
  A pending native connect now observes the configured stall deadline and
  runner stop, waits for its original promise/callback, and releases its
  socket reservation. If a failed completion cannot enter the control queue,
  its producer releases the reservation; if it already entered the queue,
  shutdown drains and releases it exactly once. A saturated local listener
  creates the pending connect without an external host or firewall.
- A writer keeps its reservation until its original reader task finishes.
  Shutdown requests reader stop, cancels receive and joins that task. A full
  peer mailbox also checks reader cancellation. The ingress source remains
  reserved until the main loop removes the socket. The test gates the
  original reader's final continuation, checks that another runner can
  admit TCP and commit a write meanwhile, and separately exercises actual
  `RunState.addSock` wiring.
- The TCP runner, acceptor and socket readers use `StopFlag`, whose private
  Boolean is accessed only under a short mutex. The pinned SDK's concurrent
  `IO.Ref.get` restores an old value after temporarily removing it; a direct
  `IO.Ref.set true` in that interval can be lost. The native regression
  pauses that actual SDK getter using GDB and lets a separate Lean task call
  the production stop request. The request survives. The C helper only
  coordinates scheduling and never writes the flag. Repeated stop requests
  remain set. Cross-thread test-fixture publications use `IO.Ref.modify`,
  which takes the SDK's exclusive ref token, instead of direct `set`.
- The app reader exposes one `Worker.requestStop` helper, used by its joining
  stop API and the app lifecycle. It publishes with atomic `modify`; the same
  forced SDK interleaving directly exercises this production helper.

Eleven negative controls must compile and fail their intended assertion: early
reservation release, omitted reader stop, omitted production reader join,
omitted connect abort/deadline/stop, either lost failed-dial reservation,
unguarded stop read, dropped stop request, and direct app-reader stop
publication. The debugger checks the pinned getter's instruction layout, actual interleaving and Linux exit status;
wrong breakpoints, debugger errors, signals and build failures never count
as a rejected mutant. The restored suites must pass.

These are runtime regressions at the native boundary, not Lean proofs that
an OS callback or dedicated thread must run. The reader continuation gate
is controlled task completion, not literal suspension of a kernel thread.
Application reservations include unfinished reader tasks; no bound on the
OS thread's final teardown after task completion is claimed. Progress still
requires scheduling, mutex holders to run and SDK/OS callbacks to finish.
The no-capability branch retains ordinary connect/send behavior (also tested),
but no cancellation deadline is claimed for Windows or failed capability
allocation. These repairs do not establish fair admission of every pending
address or an unconditional bound on every app wait.
