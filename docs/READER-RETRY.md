# Reader scheduling across failed transactions

The reader kept its pending queue inside `StateT St IO`. If a selected query
threw, the transaction rolled back and `Reader.work` kept the preceding `St`.
That restored the failed query's old position. A repeatable failure could
therefore prevent a later healthy query from being attempted.

The queue now belongs to `Reader.Shared`, outside transaction rollback.
Reconciliation and selection/removal use atomic `modify`/`modifyGet`. Removal
happens before query IO. On retry, retained requests keep their positions and
the failed dirty request joins behind them. The transaction still aborts and
rethrows its error; the repair does not continue reading an invalid snapshot.
`App.stopReader` creates a fresh Shared before starting a replacement worker,
so an old worker cannot consume the replacement's queue.

The regression runs the actual `Reader.work` loop over SQLite with synthetic
membership facts. An existing instrumentation hook throws immediately after
the same real query on three attempts. Before the repair, the later 40-member
query never published. Afterward it publishes the exact count; the failing
query produces no invented answer. A compiled control restores the scheduling
snapshot on rollback and must fail that same assertion.

The named component gate passes 82 demand checks and 34 signed-component
checks. The rollback control and the existing cancellation/remount controls
are rejected, along with both existing kernel controls. Lifecycle/node passes
39 checks; the TCP/UI regression and full 1,286-law proof audit also pass.
Separately measured scrolling has two temporary placeholder frames out of 180,
a 17.709 ms median and one-frame settling, within the unchanged test limits.
Logs are retained under `out/ci/reader-rollback-*` and
`out/component-demand/negative`. The lifecycle/proof segment ran separately
after correcting a driver target name; the named tasks and their assertions
were unchanged.

This repairs scheduling rollback, not every reader failure outcome. Transaction
opening/completion, shared journal acknowledgements and claimed action/notice
batches require their own failure invariants. Native query completion, queue
capacity, and the full write-to-display composition also remain open. In
particular, the existing early journal acknowledgement and pre-transaction
action dequeue need separate fault tests; this change does not certify them.
