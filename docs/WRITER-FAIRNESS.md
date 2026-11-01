# Local writer priority with background progress

The app's SQLite writer previously prepended every local job. Continuing
submissions could overtake an accepted local job indefinitely and prevent
background jobs from running. `Writer.submit` now appends to separate local
and background FIFO queues. Both queues and the finite phase live in one
atomic state, so a producer cannot reset the phase or overwrite a selection.
Submission updates only the selected class. Calling a generic two-list append
would traverse the other backlog even when appending an empty list in the
pinned Lean SDK; that avoidable dependency is removed.

Connected `App.submit` normally offers local ops to the TCP Runner; this
SQLite job queue serves the offline/fallback path. The checkpoint worker
remains active while connected. This queue's service laws do not replace the
separate TCP selector or establish native database completion.

`Writer.loop` calls `Writer.turn`, which calls `WriterQueue.take`. That exact
executable core calls the existing `Inbox.Priority.step`: three consecutive
local-preferred slots, then one background-preferred slot, with immediate
fallback if the preferred queue is empty. The existing FIFO interpreter was
moved from the law module into the runtime module without changing its body
or the earlier law statements. No second scheduler model determines service.

The kernel laws show that an accepted local job with p earlier local jobs is
selected within 2(p+1) completed unpaused polls; a background job with p
earlier background jobs is selected within 4(p+1). A local head therefore
waits at most one intervening poll. Every four consecutive phases prefer
local work three times. These laws allow finite arrivals between every poll
forever and require neither quiescence nor a fairness assumption on this
selector. The concrete witnesses contain nonempty signed-root job payloads,
two initially queued jobs per class, and perpetual arrivals in both classes.
Their exact first eight selections are kernel checked. Cryptographic
validity is checked separately by the native engine regression.

`mise run test:writer-fairness` builds all eleven new laws, their nonempty
witnesses and the actual native executable. It checks standard Lean axioms,
then checks twelve assertions through the real `Writer.loop`, five through
`Writer.turn`, and two through `Writer.submit`. Loop/turn checks use real
signed community roots and disk SQLite. Checkpoint callbacks gate the actual loop
after selection, allowing deterministic continuing arrivals. Catalog order
checks FIFO, local priority and background deadlines. The test also checks
retention/accounting of all accepted jobs, checkpoint-before-job ordering,
submission during checkpoint persistence, deliberate pause and resume, and
background fallback. Four controls must compile and fail their specific
runtime assertions: the old local LIFO policy, strict local priority, and a
producer that resets the phase, and rebuilding the untouched lane. The
restored suite must pass. Actual submit also checks retained native list
identity across 128-job backlogs: a local submission retains
the background lane, and conversely. This detects rebuilding the other lane;
source and generated-C inspection establish that the other lane is not
traversed. Pointer identity alone cannot exclude a discarded read-only scan,
and these checks are not a kernel cost theorem.

The task requires Linux, the pinned Lean/Rust/native toolchains, SQLite and
the user systemd manager. Lean/Lake commands use MemoryMax=48G and
MemorySwapMax=0. It needs neither networking nor GDB. Logs and databases are
retained in `out/writer-fairness`. The engine aggregate and bootstrap CI
template invoke this same named task; the template must be installed as an
active workflow before it provides CI coverage.

These are completed-selection bounds, not wall-clock or full display
latency bounds. The process must run, an intentional pause must end, and
each checkpoint/database operation must finish for later polls to occur.
The existing behavior on a job exception remains: it is logged and the
attempted job is consumed. Repeated checkpoint failure can prevent job
execution. Neither behavior is an eventual-success guarantee.

The combined UI/Writer build also passed the existing TCP flood regression
(35 assertions) and newer-page eviction regression (nine). Display took
2–62 app frames and 23–575 ms, within the unchanged 64-frame/1,500 ms limits.
The slow sample committed after 58 app frames but only three runner turns.
The old TCP starvation/hint gate passed 38 and 24 positive assertions and
rejected both controls. These are finite integration runs, not a fixed
end-to-end display deadline.

Admission remains unconditional: no accepted job is silently discarded and
no new refusal path is introduced. Queue capacity and total work remain
unbounded. List append traverses the selected class's existing queue, and a
job may contain arbitrarily many ops. Bounding memory or each iteration
requires separate admission/backpressure and job-size changes that retain
or explicitly refuse user work; this milestone does not prove those bounds.
