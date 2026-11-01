# Normal suspend and accepted local writes

`mise run test:app-suspend-journal` builds and runs the real App, Runner,
Writer and SQLite path, then three compiling controls and the restored suite.
It needs the repository Lean/Rust toolchains, fonts and a Linux user systemd
manager. Builds use 48 GiB memory scopes with swap disabled. The ready CI workflow template calls this
same task; hosted activation is still pending. logs and SQLite databases remain in `out/app-suspend-journal`.

A write accepted by `Runner.writes.trySend` leaves `App.toNode` immediately.
The App's persisted `queuedWrites` journal retains its bytes until the App
observes the operation in the store. Previously, normal suspend stopped the
runner without replaying these accepted bytes. A clean stop could leave them
in its old local lane, and a handler failure during stop could finish the
loop after suspend's initial failure observation. A new runner could commit
later writes while the earlier journal entries remained unprocessed.

Normal suspend now retains two independent tasks. `netStop` owns actual
native teardown. `netReplay` waits for the old loop's `Runner.done`, including
a late boot, then submits the captured journal to the ordinary Writer.
Loop completion is the SQLite ownership boundary; later native socket
cleanup does not access that store. Captured parked work transfers with the
journal, while later accepted writes remain parked until replay admission
and teardown complete. New runner startup observes both retained handles.
Already committed operations are replayed by ID, without adding duplicate
catalog rows. Only the existing actual-store acknowledgement retires their
journal entries.

The regression uses synthetic signed community operations and real SQLite,
not captured user data. It pauses the actual first post-commit hook, accepts
five further writes through the real bounded local channel, and begins
normal suspend while `Runner.done` is unfinished. Both clean stop and a
controlled later handler error are exercised. A third case holds the real
closing mutex: storage recovery completes while this explicit App-owned
stop-call gate remains held, and later local writes remain parked. This is
an ownership-gate test, not a claim to reproduce a blocked OS callback.

The 51 assertions inspect journal/checkpoint bytes, actual valid store
status, catalog order and uniqueness, later write progress, retained task
ownership, and resumed App publication. Controls replay only parked work,
replay before loop completion, or wait for native teardown before replay;
each must compile, terminate with exit 1, and fail exactly its matching
assertions. Build errors, signals and timeouts are failures of the gate.
The original implementation failed eight assertions across clean and
failing shutdown while still committing the later write.

This is native integration evidence. It does not prove SQLite/JNI/OS
implementations, a global frame or wall-clock bound, or successful recovery
when the store permanently fails. The replay task's own error path retains
the existing journal and reports the existing restart notice. Stage service
still requires its native operations to complete. The separate native stop
implementation owns transport cleanup; this change does not discard those
handles or reopen another runner before that cleanup finishes.

The blocking-path audit follows the calling thread separately from the full
proof wiring graph. It recognizes only the action argument of a saturated
SDK `IO.asTask`, `EIO.asTask` or `BaseIO.asTask` call as worker execution.
The replay helper is not exempted by name. The original lifecycle mutation
suite also moves this actual replay directly into `App.suspend`; the audit
must then reject its unbounded `IO.wait`, alongside the existing blocking
resume and unbounded suspend controls. This is a dependency audit, not a
proof of native task scheduling or completion.

The original lifecycle foreground-offer control initially survived because it
removed only the stop guard while the new replay guard independently protected
the same pending-loop case. That surviving run is retained. The control now
bypasses both lifecycle ownership guards and keeps the original 39 assertions,
including foreground parking. The dedicated suspend suite also holds the stop
call after replay completion, but does not clear the replay handle and re-offer
foreground work in that interval; isolated stop-only routing coverage is still
open. Neither a surviving control nor a setup error is counted as a successful
rejection.

The ready bootstrap workflow explicitly runs the original named lifecycle
baseline and mutation tasks and retains their artifacts. Its overall job
budget is 120 minutes for the expanded serial build/mutation suite; each
fixture's native timing and mutation timeout remains unchanged. Hosted
workflow activation and a cold hosted run are still pending.

A fresh private lifecycle build exposed a named-task setup gap: its wiring audit
imports proof libraries outside Main's dependency tree. The mutation task now
builds all libraries and Main itself under its own 48 GiB/no-swap scope before
running controls. The earlier missing-object failure is retained as setup
failure, not an intended negative result.

Combined-source validation passes: 51 suspend assertions with all three controls
and restoration; 77 failed-runner assertions/seven controls; 13 startup
assertions/two controls; and the original 39 lifecycle assertions, all 20
controls (six, six and eight completed groups), and restored 39/0. The setup
failure and surviving partial-guard mutation remain retained separately.
All 1,342 existing audited laws and the 689-reference README evidence inventory
pass on this integration. Full app/platform validation remains open.
