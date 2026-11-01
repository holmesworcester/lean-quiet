# Composer presentation: running policy and checked boundary

The actual composer Send path holds a FIFO of at most eight accepted messages
awaiting committed presentation. It refuses another send before submission
when full, preserves the draft and reports why. Background/bulk writes retain
their existing behavior. The oldest obligation pins its real Reader root and
child positions, so newer peer posts cannot evict it before its first paint.
Navigation, explicit scrolling and community/access changes revoke display
demand without cancelling already accepted writes.

An obligation requires the actual committed glyph/photo band in the frame;
an optimistic bitmap, blank band or placeholder is insufficient. Android and
iOS distinguish an accepted publication from its matching native completion.
The app keeps one candidate and each native bridge permits one outstanding
callback. Rejected publications preserve that candidate. Publication tickets
are independent of wrapped UInt32 input-frame serials; ticket exhaustion fails
closed. Surface replacement revokes old callbacks, including a forced generation
alias. Completion means the native API seam, not physical display scanout.

The requested UI theorem counts each pipeline stage's completed steps, not
global app frames or milliseconds. Measurements below report those native
timings separately. Reader and raster bounds must count selected stale work
as well as successful actions. Native completion is a separate wait; once its
receipt is available, the next eligible app presentation step must consume it.

## Checks

Four kernel laws cover the runtime queue bound, FIFO admission, full refusal
and exact completion identity. Nonempty witnesses construct their premises.
The existing named component, network and native-seam tasks include the new
checks and controls; the app CI gate calls those same tasks. Logs remain under
`out/component-demand`, `out/net-join` and the native seam task's output folders.
All Lean/Lake invocations must run under the documented 48 GB scope.

The isolated milestone passed:

- 79 demand checks and 34 signed-component checks; no placeholders in 180
  scrolling frames, with one-frame settling after scrolling stopped.
- 35 actual SQLite/App/Noise/TCP checks. Each composer action follows confirmed
  fresh peer traffic and queued or in-flight sync. Measured presentation was
  33–372 ms and 3–19 app frames; the limits remain 1,500 ms and 64 frames.
- Nine checks with a finite raster barrier and 108 genuinely newer signed
  posts before the first own paint. Presentation took two frames after release;
  this is not a bound on time spent behind the barrier.
- 39 native Android layer checks, including delayed completion, three rejected
  further publications, frame wrap, exhaustion and surface replacement.
- Nine compiled UI mutations and 12 compiled native mutations rejected at their
  intended assertions; build errors, crashes and unrelated failures do not pass.
- Existing lifecycle checks and 292 desktop checks/27 renders remain passing.

The integrated main-worktree run also passed the 35 TCP checks: commits and
read-backs took one or two app frames, and displays four to six frames
(161–267 ms). Its nine eviction checks inserted 110 genuinely newer posts;
the own message displayed two frames (68 ms) after the finite raster barrier
was released. The full proof gate checked 1,261 laws. These are additional
finite runs, not stronger universal bounds. The integrated component run
passed 79 demand and 34 signed-component assertions; all 180 scrolling
frames had pixels, with an 11.912 ms median and one-frame settling. All
19 component runtime mutations and both kernel controls were rejected.
The app gate completed in initial/resumed stages after updating stale UX
mutation anchors; lifecycle, safe-area, desktop/Linux and Windows input
checks passed. Retained baseline/mutant logs also pass the strict crash guard.

Fixtures use synthetic users with real signatures, not captured community data.
The iOS shared C gate is exercised by the host tests; the Objective-C wrapper
has source review only here, without an Apple SDK or device run. Combined Android
Activity-recreation checks remain required after integration of that repair.

## Still open

The subsequent [desktop publication repair](DESKTOP-PRESENTATION.md) removes
the premature staging acknowledgement. It validates final composed pixels and
actual native completion, including hover/photo content. Its Linux runtime
checks and Windows cross-compile are separate from still-outstanding Mac and
Windows native runtime validation.

The stage-local UI theorem still needs Reader/raster service ranks, bounds on
their admitted predecessors, retained-paint invariants and composition with
commit and receipt handling. The eight-entry composer FIFO does not bound all
Reader/raster jobs. Native workers and callbacks need explicit progress or
cancellation contracts; their delays are separate from completed-stage counts.
Reaction cardinality, history queries and other frame work also lack a uniform
work bound. A lost callback can retain
the single callback slot across a surface reset until it returns. Exhaustion
fails closed but does not establish successful presentation of every send.
Touch lookup still matches retained Nat serials against UInt32 native serials;
the independent completion ticket fixes presentation aliasing only.
