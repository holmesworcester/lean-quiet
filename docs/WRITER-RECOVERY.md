# Preserve writer ownership through returned failures

`Writer.commitSave` now attempts a checkpoint once per service turn. A failure
retains its generation and payload, with the original 50 ms error backoff, then
allows the selected job to run. A newer checkpoint can still replace the older
pending value. The previous recursive retry blocked healthy writes whenever
only the checkpoint table was unavailable.

A checkpoint-only repair exposed another loss: a whole-database lock made the
selected job fail, and the old catch discarded it. `Writer.turn` now keeps its
busy ownership and returns the job to its own class's FIFO tail. It neither
increments busy again nor resets the 3:1 selector phase. Healthy local and
background jobs proceed, and the retained job commits after its SQL fault is
removed. The existing queue laws bound selection, not successful SQL completion.

`Writer.submit` and `App.submit` also refuse empty operation batches before
accounting or queue admission. A real keyless `Community.unwrap` produced such
a batch; 100 calls had accumulated 100 writer jobs or parked batches while the
encoded pending-op count remained zero. Nonempty signed controls still commit.
This closes that bypass; it does not establish a cap for all nonempty queues.

Checkpoint and job diagnostics now contain returning IO errors. Actual
`stderr=/dev/full` previously unwound a selected checkpoint turn before its job
could run. The repaired path commits the signed op and retains failed jobs even
when error reporting itself fails. This does not make a blocked log sink
nonblocking.

## Gates and limits

`test:writer-job-retry` builds the actual runtime and runs 10 empty-batch,
11 selective-SQL and 11 OS-diagnostic checks. All nine compiling mutation
controls and the restored 32 checks pass on the combined primary source.
`test:writer-checkpoint` passes 12 checks and rejects the old recursive behavior
with a completed six-pass/six-failure control, then restores all 12 checks.
The combined primary source passes both named gates, including restoration.

Private compatibility also passes the original Writer fairness checks and four
controls, the four native publication cases and controls, and the original
39 lifecycle assertions. The intermediate checkpoint-only change failed two
of those assertions; the final patch preserves the original oracle. Initial
control/setup compile failures are retained and never counted as rejections.
The corrected phase-reset control mutates the actual `slot` field.

The full engine suite and ready bootstrap workflow invoke these same named
Mise tasks, including build/setup. Linux `/dev/full`, pinned Lean, systemd user
scopes, crypto/SQLite and font assets are required. Fresh databases and logs are
retained under `out/writer-job-retry` and `out/writer-checkpoint`; every build is
capped at 48 GiB with swap disabled. The workflow template remains inactive.

These are runtime ownership repairs using the existing queue policy, not a new
whole-worker theorem. Failed jobs may retry forever. Successful retention needs
storage progress/capacity; terminal user outcomes under permanent failure,
blocking diagnostics, queue capacity and outer App rollback remain open. No
universal wall-clock or end-to-end UI latency bound is claimed.
