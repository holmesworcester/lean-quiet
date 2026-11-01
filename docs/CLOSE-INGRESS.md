# One admitted frame at transport teardown

The actual TCP reader admits at most one frame per fixed ingress source. A
writer failure can publish `.closed` through the separate control source while
that frame is still queued. The previous control handler and completed-writer
reaper invoked Node.close immediately, erasing keys and canceling the mailbox.
A preserved production Noise/SQLite trace lost a signed removal notice in five
of eight cases. The receiver's session was only one millisecond old; this was
not silence expiry or an abstract delay-after-TCP-close schedule.

`Registry.freeze`, called by `Hub.freeze` inside the same mutex as offers,
returns the admitted value and disables future admission while preserving the
source owner and selector state. `RunState.transportClosed` stops further I/O
and retains a `closeAfterFrame` obligation only for an already-admitted frame
from that socket. Repeated close/reap observations cannot replace or renew it.
The real frame handler closes afterward, including invalid-input refusal.
Explicit authenticated retirement, protected-output overflow and global
shutdown still close directly. In particular, new critical output for another
session sharing the address is outside this retained-input guarantee.
The later tick/expiry phases preserve this one obligation. Exceptional frame
processing retires native ownership before attempting SQL cleanup and preserves
the original exception; durable erasure is not promised while writes fail.

Six unconditional kernel laws cover the executable registry operations. They
preserve the captured value, source ownership, state and poll result, refuse
future offers and make freeze idempotent. All six are instantiated on a live,
nonempty source in tests/vacuity/IngressFreeze.lean. Full IO trace refinement
and native task completion are separate from these helper laws. The existing
priority/ingress bounds count completed stage steps, not wall-clock time.

## Named regression

Run `mise run test:close-ingress`. It builds the native target and kernel
witness, then runs the baseline, strict mutations and restored baseline. CI's
engine and bootstrap tasks invoke this same task. Linux/POSIX loopback TCP,
the pinned Lean SDK, Rust crypto and SQLite build prerequisites are required;
no external service or collected user data is used. Logs and fresh databases
are retained under out/close-ingress. A compile error, timeout, signal, crash,
setup failure or unrelated assertion cannot count as a successful runtime
mutation control.

The actual fixture uses signed bootstrap, Noise/AEAD, Node, SQLite and TCP.
It forces both control and completed-writer orderings with the authentic notice
already admitted, then runs the normal Loop.turn under continuing local writes.
A separate invalid frame proves teardown is not merely a consequence of the
valid removal notice. Signed local removal bypasses the retained peer input.
Actual SQLite query_only and post-commit notification faults test exceptional
cleanup. A bounded Hub fixture observes a real full offer before freezing,
refuses a later flood, retains ownership and checks safe source reuse.

The exhausted-grace/zero-deadline branches deliberately supply runtime states
to test same-turn timer behavior; they are state-level branch coverage, not a
fixed-configuration end-to-end trace. The native gate currently passes 40
checks, rejects nine compiling runtime controls and one unchanged-kernel
control, and restores all 40 checks. The original expiry suite passes 29
checks, two controls and restoration with its original deadlines.

## Compatibility evidence

These private-source results use ce76360 plus the retry and Fresh fixture repairs.
These results are distinct from the combined-source checks below. All builds ran with
MemoryMax=48G and MemorySwapMax=0; native tests used host
cores 16–21. Counts below are fixture checks and rejected controls, not claims
about all executions. Elapsed-time oracles were unchanged.

| Gate | Positive checks | Controls and restoration |
|---|---:|---|
| close-ingress | 40 | 9 compiling runtime + 1 unchanged kernel; restored 40 |
| expiry-grace | 29 | 2; restored 29 |
| ingress | 68 | 8; restored 68 |
| native-lifetimes | 26 | 11; restored 26 and SDK stop probes |
| fresh | 53 TCP | 19; restored native suite |
| retry-admission | 29 | 5 runtime + 1 kernel; restored 29 |
| reserved-retry | 12 | 4 runtime + 1 kernel; restored 12 |
| join-fair | 38 main + 24 hints | Existing three progress/order controls |
| harden | 156 + 11 TCP | 24; restored suites |
| simplify | 34 | 25; restored suite |

The full private audit completes 358 library and 263 Main build jobs and checks 1,317 laws
against standard Lean axioms only; doors, inventory and README wiring controls
pass. The exact committed Fresh startup prerequisite is 9e12137, separately
packaged; its two completed-turn setup barrier preserves the old action
oracles. The ingress/reader fixtures retain the original quota assertions,
then consume the actual frozen frame before requiring source reuse. A stale
native-lifetime footer was corrected from 24 to 26; both its baseline and
restoration already required and reported 26.

The earlier failed removal run, eight-case causal trace, and strict-test
setup failures remain in the evidence archive. No compilation failure or
fixture exception was accepted as a successful runtime mutation.

## Remaining boundaries

Protection starts when transportClosed freezes an admitted source. Bytes still
in OS buffers, earlier timeout orderings, arbitrary socket/session replacement
and full fair-loss convergence remain outside this result. Node.step(.close)
still erases immediately; the native adapter delays calling it for one finite
input obligation. The broader app currently logs a failed runner task, and its
blocking Runner APIs cancel, but direct App write offers do not observe failed
runner completion. Recovery or visible action failure for that path is an
independent open obligation. This repair makes no whole-app memory/work bound
or universal native timing claim.

## Combined-source integration

On the primary source after `215da26`, both transport patches preserve the
newer Reader, placeholder cache and owned-input changes. The full kernel gate
passes all 1,330 laws using standard axioms only. `test:retry-admission` passes
29 checks, five compiling runtime controls, one kernel control and restoration;
`test:close-ingress` passes 40 checks, nine compiling runtime controls, one
kernel control and restoration. The original `test:expiry-grace` passes all
29 checks, both controls and restoration. Logs are
`out/ci/transport-integrated-{proof,retry,close,expiry}.log`.

The complete evidence dependency/axiom audit and its runtime certificates pass,
as do all eleven inventory checks and the README wiring controls. The short
placeholder theorem alias now points to its existing checked witness: 684
reference labels have evidence, including 14 explicitly conditional entries.
This does not add a distinct placeholder theorem. Broad combined app, Android
and desktop suites remain separate validation; these component gates are not a
whole-app convergence proof.
