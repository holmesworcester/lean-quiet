# Shared publication regressions

Up to Lean 4.34, the SDK could lose a direct `IO.Ref.set` to an overlapping
getter that restored an older value. TCP and app reader stop publication are covered
by [the native lifetime gate](NATIVE-LIFETIMES.md). The follow-up
`mise run test:ref-publications` covers four additional running paths:

- `Writer.commitSave` atomically publishes its completed checkpoint number.
  Previously the SQLite checkpoint could commit and its pending payload be
  cleared while an old getter restored the previous acknowledgement. Later
  writer passes then had no pending payload to retry, so `saveDone` could
  remain false. The regression uses actual `Lifecycle.save/load` on disk,
  checks the exact checkpoint through another connection, and checks both
  another idle commit pass and a later changed checkpoint.
- `Writer.setPaused`, used by the app's pause/resume controls and suspend,
  publishes atomically. The test pauses the actual writer loop's getter,
  resumes it concurrently, and requires queued signed community roots to
  become valid stored ops. Deliberate pause still retains a later queued job
  until an explicit resume. An iteration already past its pause check may
  still take a job; the deliberate-pause check lets that iteration settle.
  The fixture exits its owned process after the
  assertions because the production writer loop intentionally keeps running.
- `Writer.noticed`, used by the app's journal reader, atomically publishes
  the shared acknowledgement. `Writer.pruneOnce` contains the same database
  effect called by the five-second prune loop. The test forces an old prune
  snapshot to overlap publication, then requires the next actual prune pass
  to remove the acknowledged journal rows while retaining the valid op.
- `Reader.pass` atomically publishes its shared journal position. Its test
  runs the real pass against journal rows produced by a valid signed root.
  It checks both the publication and an idle later pass, then checks that
  those rows can be pruned. An idle pass did not repair a lost acknowledgement
  because the reader's internal position had already advanced.

Each case pauses the actual SDK getter with GDB and uses the running
production operation as publisher. The four cases must pass;
debugger/layout errors, signals, timeouts and build failures fail the gate.

**Lean 4.35.0 fixed the race.** In Lean 4.35.0 (2026-10-12; lean4 #14775
and #14585), `IO.Ref.set` waits until an overlapping `get` has put its value
back, so a set can no longer be lost. The four old direct-set mutations no
longer fail, so they were dropped. We keep the atomic `modify` publications
anyway: they cost little, and they do not depend on that fix.
Logs and SQLite databases remain under `out/ref-publications`; a timeout
terminates only the test command's owned debugger/inferior process group.

The named task builds its crypto and Lean prerequisites. It shares the Linux
x86-64, pinned SDK, GDB child-ptrace and systemd-user requirements of the native
lifetime gate. Every Lean/Lake build is capped at 48 GB with swap disabled.
The engine and bootstrap-progress gates invoke this task; their CI template
retains its artifacts. Installing the template under `.github/workflows` is
still required before that workflow runs on GitHub.

These are causal native regressions, not proofs of OS scheduling, SQLite
completion latency, bounded journal size or every shared-state invariant.
The detached old-reader cleanup resets are unchanged: this audit found no
concrete loss of durable work from those resets, and its in-flight action
results still use atomic transfer through the retained retired board.

App lifecycle, admission, composer and component fixtures now use the same
atomic pause/resume helper as production. This avoids losing their deliberate
writer gate to the writer loop's concurrent getter; assertions and deadlines
are unchanged.
