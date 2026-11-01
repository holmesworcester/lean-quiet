# Visible request selection bound

`Demand.take` and `takeBy` are executable selection-and-removal operations. The actual Reader and Work worker call them. `DemandRank` proves that a continuously visible queued target is selected or explicitly retired within `p + 1` selection attempts, where `p` is its number of preceding queue entries immediately before the first counted selection. The visibility premise applies only while the target remains queued inside that finite window. Continued ownership for the window excludes the retirement alternative; nothing is assumed about visibility after the window.

These are universal trace laws over transitions that call the actual runtime helper, followed by filtering and FIFO admissions. They are not a full refinement proof of the asynchronous IO worker or Reader transaction loop. The theorem conclusion names `Demand.take` directly; no extra runtime reachability is asserted for a proof-only accessor.

All preceding entries count, including background entries that become visible later. Arbitrary intervening removals, visibility changes of other entries, and finite FIFO tail admissions are allowed at every step. New work need never stop. These are selection bounds; they do not bound queue capacity, list traversal cost, SQLite/native duration, or background service during unlimited visible arrivals.

`Work.stats.completedSelections` counts a selected entry after its ownership/action path returns: success, continuation, caught exception, and canceled selection all count once. An in-flight action, paused poll, and idle poll do not count. Existing `stats.steps` retains its action-attempt meaning. Selection precedes action completion. Sampling a queue rank at arbitrary admission can find an already selected action in flight; its later completion adds one counter increment outside the sampled queue. A claim about a counter delta from admission must account for that offset. The kernel bound is indexed immediately before selections, not by arbitrary admission snapshots.

Reader uses the same operation, but this lemma alone is not a proof of whole Reader progress: opening a transaction, processing acts, reconciliation, query execution, and transaction completion are separate stages. Failed queries must not restore their queue position; the independently tested Shared-owned queue repair addresses that rollback boundary. Other transaction/shared-publication failures remain outside this selection result.

The nonempty kernel witness starts with four entries, promotes an earlier background entry, retires another predecessor, and admits fresh work forever. The retained target is selected on attempt 3, within its initial bound of 4. Seven laws and their concrete applications have only standard Lean axioms.

Run `mise run test:demand-rank`. It builds a private copy of the actual production Demand/Work closure and retains logs in `out/demand-rank`. Thirteen real-worker checks exercise ongoing admissions, visibility priority, queued retirement, in-flight cancellation, continuation and exception accounting. Four mutations must compile and fail their intended assertions: newest-visible selection, prepend admission, background-first selection, and premature pending-action accounting. The newest-visible change must also fail the running selector's rank proof. Restored source must pass again.

Prerequisites: the pinned Lean toolchain, Python 3, a C toolchain, and a systemd user session supporting `MemoryMax=48G` and `MemorySwapMax=0`. Every Lean/Lake invocation in this task has those limits. The engine gate and bootstrap-progress workflow call this same named task; the workflow remains a template until repository credential/deployment setup enables it. No native timing result is inferred from this suite's test deadlines.


Integrated validation passes the full 1,294-law audit, all 670 vacuity entries
with runtime certificates and controls, 82 demand checks, 34 component checks,
four related worker/reader runtime controls, both existing kernel controls,
and 39 lifecycle checks. The README gate initially required its explicit
“Not yet” wording; corrected metadata passes without any theorem change.
Logs remain in `out/ci/demand-rank-integrated.log` and
`out/ci/demand-rank-metadata.log`. Separately measured scrolling has two
temporary placeholder frames out of 180, a 14.052 ms median and one-frame
settling, within the unchanged regression limits.
