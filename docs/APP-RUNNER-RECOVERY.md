# Recover accepted writes after a network runner failure

The actual App now checks a finished installed Runner before offering writes,
including the empty parked-queue path. `flushNode`, `netStep` and `suspend`
detach it, clear automatic reconnect configuration, and report sync failure.
The accepted-write journal covers both parked operations and operations already
accepted by the failed runner's channel.

A retained task decodes and submits that journal through the ordinary local
Writer. Later local actions stay journaled and parked until replay admission
completes, preserving submission order. Actual store observation retires the
journal entries; replay admission alone does not. Replaying an already committed
operation is idempotent by operation ID, not a claim of exactly-once IO.

The failed runner's retained stop task has a separate handle from normal
suspension, so it does not suppress active App frames. Lifecycle polling observes
both tasks under the existing shared suspend deadline. Replay failure reports a
notice and retains the journal for restart. No automatic reconnect is attempted.

## Regression and source boundary

`mise run test:app-runner-failure` builds the actual App/Runner/Writer/SQLite
fixture and runs 77 checks, seven compiling controls and restoration. The
combined primary-source gate passes all assertions, controls and restoration.
The original fixture completed with six passes and nine failures. One signed op
commits before a gated hook throws, a second is stranded in the real channel,
and a third arrives after failure. A test-only SDK queue-token gate checks
ordered admission off the App thread. A real closing-mutex gate holds the
App-owned stop call while actual App frames and local commits continue.
Neither a timeout nor a failed build is accepted as a mutation rejection.

The engine suite and ready bootstrap workflow invoke this same named task.
Linux, the pinned Lean SDK, systemd user scopes, native crypto/SQLite and font
assets are required. Logs and each fixture database remain under
`out/app-runner-failure/negative`; builds use MemoryMax=48G and no swap. Hosted
workflow activation remains separate from the checked-in template.

This is runtime regression evidence, not a new universal Lean theorem. Native
ownership after arbitrary runner exceptions is a separate repair. The normal
suspend journal race is addressed by [APP-SUSPEND-JOURNAL.md](APP-SUSPEND-JOURNAL.md),
and startup under continuing writes by [APP-BOOT-ADMISSION.md](APP-BOOT-ADMISSION.md).
Writer job errors are addressed by [WRITER-RECOVERY.md](WRITER-RECOVERY.md).
Arbitrary IO noncompletion, permanent storage failure, outer App StateT rollback
and general queue capacities remain open. Stage bounds count completed steps;
native timing is measured separately.
