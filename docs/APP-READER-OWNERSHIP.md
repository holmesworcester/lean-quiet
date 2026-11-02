# Reader worker ownership across App errors

`mise run test:app-reader-ownership` builds and runs the actual App, threaded
Reader worker, Writer and SQLite fixture, compiles six causal controls, and
restores the baseline. The engine suite and the ready bootstrap-progress
workflow call the same task; hosted workflow activation remains pending. It
requires the repository toolchains, fonts, a Linux user systemd manager and
native SQLite/crypto. Each build runs in a 48 GiB scope without swap. Logs and
SQLite databases remain in `out/app-reader-ownership`.

The threaded Reader worker was created by `Reader.Worker.start` and recorded
only in the returned `App.St`. When a later frame callback threw in the same
outer StateT, the App lost the only handle to that worker: suspend could not
revoke it, the in-flight pass could still publish, and the worker's SQLite
connection was never reaped. A completed reap could likewise be discarded by a
later callback error, losing the only reusable Reader connection.

App now allocates one shared `Reader.Owner` beside the network owner. It has
fixed slots for the active worker, one retiring worker, the replacement board
and the recovered connection, plus a generation counter. The frame's existing
`reader`, `readerStop`, `retiredBoard`, `sh` and `rst` fields are borrowed
views refreshed by `syncReader`. The worker thread is created and registered
in one `BaseIO` claim under the owner's mutex; no database action, join or
user callback runs under it. Unmount revokes the original worker before
installing a fresh board, and a repeated unmount keeps the same retiring task
and board. Acts not yet run move to that replacement board (on a repeated
unmount, back onto the same board) ahead of any appended since, as main's
unmanaged path carries them to its fresh board. A completed worker is reaped into shared ownership, so a later frame
error cannot discard its connection. Synchronous twins never register a board,
so `syncReader` leaves their local Reader state alone. `query`, `writeAll`,
`act` and `readerPass` keep their mounted/lease checks first; they refresh the
borrowed view only after those checks admit the call.

The 26-check fixture blocks the actual threaded Reader inside an admitted
intent, throws from a real frame callback after `mountPage`, and discards the
failed StateT result. Suspend from the stale state must still revoke and
retain exactly the original worker; repeated suspend keeps the same retiring
task, board and generation; no replacement starts while the original is held.
After release, the revoked pass must not publish its signed write. A screen
callback then throws after reaping; the shared owner must still hold the
original connection. Re-entry from stale fields recovers that connection, the
fixture commits a signed op through the actual Writer and reads its bytes back,
and a replacement worker publishes them through its board before shutdown.
Pointer equality is used only by the test to observe Task and Ref identity.
The signed data is synthetic.

The six compiling controls forget the active slot, forget the retiring slot,
omit revocation of the original worker, let repeated suspend replace the
retiring generation, discard the reaped connection, or reset synchronous cache
progress on every poll. Each must exit 1 with its exact expected assertion
list. A compiler error, crash, unexpected exception or timeout is a failed
gate, never a successful control. The restored source must pass all 26 checks.

This is native regression evidence about resource ownership, not a kernel
proof of the FFI or universal App exception safety. It does not make one-shot
notices or writer admissions exactly-once across rollback. A worker whose pass
returns an error is not reaped and keeps its retiring slot. Native callback
completion and SQLite progress remain separate obligations.
