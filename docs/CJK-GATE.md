# CJK gate failure reporting

The full app attempt on `8bd282c` reached the actual 500-post CJK scroll and
failed its unchanged 16,667 microsecond p95 step limit: median 14,893 us,
p95 29,228 us, 547 frames. Its final image had been written, but the test then
waited indefinitely during Lean task-manager teardown. The writer and pruner
were still running their permanent loops. A captured native stack identifies
that wait; flushing the blocked process recovered its buffered measurements.
The test process was then terminated, so that full app attempt failed.

`CjkScroll.main` now catches test errors, flushes the measurements and error,
and exits with status 1. The regression injects an error after actual
`App.start` has started those writer tasks and requires the precise error and
exit status within 15 seconds. A timeout, crash or unrelated failure fails the
regression. `host:cjk` builds the runner and runs this check before the existing
font and scroll checks; the app CI task invokes that same named task.

The failure-reporting regression passes. The subsequent full CJK task reports
its performance failure promptly: median 16,318 us, p95 30,663 us, 547 frames.
Both attempts ran alongside other builds; no causal attribution to contention
or a particular app change has yet been established. The original scroll
threshold, workload and image checks are unchanged. Performance repair and a
passing full app gate remain outstanding. This test-entrypoint repair does not
prove general writer shutdown or app deadlock freedom.

Evidence is retained in `out/ci/owned-input-full-app-8bd282c.log`,
`out/ci/cjk-scroll-8bd282c-stacks-root.log`,
`out/ci/cjk-scroll-8bd282c-flush.log`,
`out/ci/cjk-failure-reporting-fixed.log`, and
`out/cjk-failure/failure.log`. The initial wrapper type-check error is retained
separately in `out/ci/cjk-failure-reporting.log`.
