# Reader acknowledgement follows its transaction

The running Reader now publishes its journal cursor only after the final SQLite `COMMIT` succeeds. It is the last effect before the successful pass returns its already-built Reader state. The threaded worker assigns that state without intervening IO. A query or commit failure therefore leaves the journal notices needed to invalidate the retained cache available to the pruner's next acknowledgement check. The prior Shared-owned scheduling queue repair is preserved.

The native regression warms a real SQLite cache at 40 members, commits a 41st member with actual trigger-generated filings, and throws through the existing `afterQuery` seam during recalculation. It retains the same old state that the worker keeps on an exception, takes the UI connection's actual journal snapshot, then calls the production `Writer.noticed(min …)` and `Writer.pruneOnce`. Before this repair the shared cursor advances from 200 to 205 despite rollback, pruning erases the new notices, a cold SQL read returns 41, and the healthy cached retry stays at 40. After the repair the failed cursor remains 200, four dependency filings remain, and the retry returns 41 before acknowledging and pruning them.

The fixture directly seeds admission facts, as the component member-count tests do; it does not test signatures or admission authorization. This is actual Reader/pass/pruner evidence, not a refinement theorem for every asynchronous worker or whole App frame trace. Earlier side effects to outboxes, action results and popped acts/notes are separate failure boundaries. An outer frame rollback after a successful pass is not proved safe by this change.

Run `mise run test:reader-prune`. Nine checks use separate real SQLite connections. A scratch mutation must compile, move the acknowledgement back before queries/commit, and fail the exact stale-count assertions (5 passed, 4 failed). Restored source must pass 9/0 again. The named task builds its native target and runs the same strict control in local engine CI and the ready bootstrap workflow template; enabling the hosted workflow remains a separate repository setup task. Logs and each baseline, early-ack mutant and restored SQLite database (including failures/timeouts) remain in `out/reader-prune/negative`; runtime artifacts are copied before scratch cleanup. Lean/Lake builds are capped at 48 GB with swap disabled; prerequisites are the pinned toolchain, Python 3, C/Rust toolchains, the repository crypto dependency and a systemd user session. No timing deadline or journal assertion is weakened.


Integrated op-tree validation passes the same nine actual SQL checks, the
compiled early-ack control and restored run. All three database artifacts are
retained. The complete 1,294-law audit, 670-entry vacuity gate with its runtime
certificates/controls, 82 demand checks, 34 component checks and 39 lifecycle
checks pass. See `out/ci/reader-prune-integrated.log`.
