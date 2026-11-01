# Foreground UI during normal network cleanup

Ordinary App suspend retained the network cleanup task correctly but used its
presence to suppress the entire foreground frame, mounting and Reader startup.
A delayed native cleanup therefore also stopped typing and reading a conversation.
The actual Runner fixture reproduced five failures while holding the original
Runner's closing mutex; it completed seven other assertions and exited 1.

The App now admits foreground frames, mounting and Reader startup independently
of that network task. Reader connection ownership and cancellation remain
separate. `submit`, `flushNode` and `netStep` keep their stop/replay guards:
accepted writes retain order, and no replacement Runner starts early. Original
native cleanup handles remain owned until the same task completes.

`mise run test:app-stop-ui` builds the actual App/Runner/SQLite fixture, checks
12 assertions, restores each of the three old UI guards as a compiling negative
control, and runs the restored baseline. The first completed foreground stage
publishes a frame and mounts the conversation; the next stage accepts typing.
The actual threaded Reader publishes SQLite answers while cleanup is still
held. The fixture checks original task identity, parked signed writes, later
commit and native listener cleanup. Its conversation and messages are synthetic.

On the merged source (origin/main `149943e` plus the network, frame-time and
Reader ownership repairs) it passes all 12 checks, the three exact-failure
controls and restoration. The lifecycle-node fixture asserted the old
behaviour (no frame while teardown is pending); it now expects exactly one
resumed frame and still checks that no runner starts and no parked write is
offered early (40/0, all controls). The engine suite and the ready
bootstrap-progress workflow invoke the named task; hosted activation remains
pending. It requires the repository toolchains,
fonts, Linux user systemd and native crypto/SQLite. Every Lean/Lake build uses
a 48 GiB/no-swap scope. Logs and databases remain in `out/app-stop-ui`.

These are completed-stage observations and regressions, not a universal
write-to-display theorem. Native milliseconds are reported separately. A
returned normal cleanup error can still throw from polling. Reader creation
across outer StateT rollback, native callback completion and recovery of
permanently blocked or failed storage remain separate obligations.
