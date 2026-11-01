# Native ownership after runner failure

The actual runner could accept a TCP socket and start its reader/writer in the
primary event, then throw during the same turn's timer hook. `Loop.turn` never
returned the updated `RunState`. Even sockets from earlier completed turns were
lost when the runner task ended. Calling `Runner.stop` stopped the listener but
had no remaining socket handles to cancel or join.

The preserved causal run used real TCP, SQLite and `Runner.start`: one idle peer
completed a prior turn, a second peer was accepted in the failing turn, and the
actual hook threw. The original error was observable and counters recorded
10 started / 9 completed turns, but both native leases remained held and neither
peer saw EOF after `Runner.stop`. The diagnostic process subsequently timed out;
that timeout is evidence of the old leak, not an accepted mutation result.

## Actual ownership and cancellation

`JobOwners.launch` now retains original dial and socket-writer task handles
outside whole-turn state publication. A socket writer already owns and joins
its original reader through `finishReader`. Registration only prunes tasks for
which `IO.hasFinished` is true. The table has at most `2 * cfg.maxSocks` entries:
a successful dial can post its completion event before its original task ends,
so the handoff can overlap that original dial and the new socket job. This is a
bound on registry entries, not a whole-app heap, underlying SDK buffer, native
completion-time or per-turn-work theorem.

The actual `JobOwners.admit` helper tests capacity before running its factory.
The factory is `BaseIO` and only creates tasks/records, so it cannot raise a
recoverable IO exception between task creation and registration. Fallible socket
capture occurs first. Refusal retires the reserved ingress source, closes the
still-idle client and releases its socket quota. Refused dial startup keeps its
waiting destination and releases its temporary quota reservation.

On a loop exception, the runner immediately stops ingress and requests native
cancellation. These requests neither join native tasks nor access SQLite. The
listener observes the same cancellation; each socket reader is stopped and its
source retired. Ordinary writers are woken and stopped. Already-retiring writers
retain their bounded queued notice and existing native-send deadline. There is
no producer left that can extend that drain. The original loop error is rethrown;
failure to write its diagnostic to stderr cannot replace it.

One fixed teardown task per real runner owns the joins. After loop completion it
joins the listener and every retained original job, then closes queued accepted
or dialed clients that never entered `addSock`. `Runner.stop` requests stop and
awaits that same task. Cleanup runs even if no caller observes the runner error.
The write channel and its queued operations remain untouched by the exception
cleanup; application recovery and durable journal replay are a separate change.

## Validation and proof scope

`mise run test:runner-ownership` builds the actual native executable and three
helper laws, checks nonempty successful/refused stateful factories, runs 24 native
assertions, and requires ten runtime mutations to compile and fail their named
assertions plus one unchanged-kernel rejection. It repeats the original-error
case with stderr actually redirected to `/dev/full`. A restored 24/0 run is
required. `test:engine` and the ready CI template’s `test:bootstrap-progress` call the same task and
retain `out/runner-ownership` logs. Linux/POSIX TCP, `/dev/full`, pinned Lean/Rust,
C/SQLite prerequisites, and a user systemd manager supporting the 48 GB/no-swap
scope are required.

The runtime cases cover an earlier peer, a socket accepted in the throwing turn,
a queued raw client, cleanup without calling stop, a real successful dial held
at its task tail, an actual retired writer held before sending its notice,
original-task joins, bounded factory refusal, and actual `addSock` refusal cleanup.
The held continuations are explicit component scheduling gates, not claims about
native wall-clock bounds. Mutants cannot pass by crashing, timing out, failing to
compile, or missing setup. Tests explicitly exit after recording the final
assertions so intentionally orphaned mutant tasks do not prevent a failing test
process from reporting its result.

The kernel laws prove the running admission gate's insertion bound, pure refusal
without executing its factory, and use of the exact supplied factory when room
exists. They do not prove complete concurrent IO trace refinement or eventual OS
callback completion. Supported POSIX cancellation still depends on OS scheduling
and native callback completion. Windows retains the existing SDK completion
path without a cancellation bound. A handler that never returns, durable SQL
recovery after an exception, and application-level failure/replay outcomes are
outside this native ownership repair.

Hosted workflow activation remains pending. On the combined primary source,
the named task passes all 24 assertions, ten compiling runtime controls, its
kernel control and restoration; the actual /dev/full baseline/restoration also
pass 11 assertions each. The 1,355-law audit and all 707 evidence entries pass.
Actual App recovery also passes 77 checks/seven controls and normal suspend
51 checks/three controls, with restoration. Full app/platform
validation and the persistent-session policy follow-up remain open.
