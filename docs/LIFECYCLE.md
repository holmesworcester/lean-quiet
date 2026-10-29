# Lifecycle inventory

The lifecycle implementation is `ops/app/Lifecycle.lean`, `AppLife.lean`
and `ops/app/LifecycleLaws.lean`. `AppTypes.lean` is a mechanical extraction of
the app's types, needed to share them with the hooks without an import cycle.
`App.lean` retains the root, page actions and existing proved functions.
`Kinds.Message.read` and its read order are unchanged.

## State and ordering

The durable checkpoint is a canonical, content-addressed local op (kind 239)
in `app_ops`, a journal in the **same SQLite database** as the engine's ops.
The table is deliberately outside the sync family's index: these ops never
enter sync, and cannot be injected through the network. Its local sequence
orders checkpoints. It is not a new shared Community or Connection kind.
The existing family and its proofs are unchanged.

Durable fields: the selected **acceptance**, page/back stack, per-acceptance
composer text and photo bytes, page field, invite/name/create flow, removal
confirmation or sending state and target, issued invite links, reader window,
and the anchor's message id and top-edge distance. Joining, admissions,
removals, messages and keys remain the existing engine ops. A write intent
is in the checkpoint handed over before it is enqueued; startup replays
journaled intents by op id before reading accepted communities. Repeated
replay is idempotent. Each changed checkpoint is handed to the writer's
thread before the event turn returns (`Data.Writer.save`); the writer
commits the newest one, before any job submitted after it, and suspend's
deadline covers that commit. A failed checkpoint is retried on the writer
before its following job runs; a temporary SQLite write lock cannot make
the writer attempt and discard that job. The frame never commits: it holds its read
transaction all turn, and a node's `wal_checkpoint(TRUNCATE)` (a purge's)
holds SQLite's write lock until every reader finishes, so a commit on the
frame waited on the frame itself until the busy timeout threw out of
`App.step` (the `block Lifecycle.save` note in tests/wiring.txt). There
is no dependence on a final OS termination callback.

Ephemeral: keyboard height/composition, selection, reaction sheet/velocity,
query cache and subscriptions, mount generations, row/image/QR tasks,
camera frames, toasts and scroll velocity. These are rebuilt, not restored.
SQLite process-crash atomicity is tested; power-loss durability and the
native SQLite implementation are still part of the seam. The journal is
append-only; retention/compaction is a follow-up.

Suspension: the native shell immediately stops presenting and closes its
camera/keyboard; Lean captures the final native text, revokes the page,
detaches the reader's board, starts runner shutdown on its own thread,
and checkpoints. Suspend polls all teardown work against one absolute
250 ms deadline. A timeout means cleanup is still pending, not quiescent;
its handles stay owned, as do every parked write and unfinished producer. A background step only receives
lifecycle/URL events; it performs no page reads, writes or frame submission.
Foreground and a surface are both required to resume. Lean reads the current
viewport, mounts, re-reads current facts, starts sync, resumes the scan page's
camera, and submits a frame. The camera permission flow can cause another
pause/resume; Java does not independently reopen the camera.

Root reads are synchronous on the app thread, so navigation cannot interleave
inside a root SQLite read. The dedicated reader is signalled and its shared refs are detached. Each subsequent query and board publication
checks revocation; a SQLite read already issued may finish on the old refs. Queued callbacks carry a mount generation; work from
an earlier mount is rejected, including after remounting the same page.
Paint/QR/image workers are pure and cannot publish into app state themselves.
Unmount retains unfinished pure workers for later reaping; their results
cannot publish into the new page. Normal navigation and resize never join
them. Suspend alone may poll, bounded by its deadline. Already accepted durable writes belong to
the store and can finish after navigation; no new write can be issued by
the revoked callback.

`Mount.tree` records the root's queries and each mounted row's queries.
Cached reads register ownership too. Every turn prunes `Live.entries` and
`Live.subs`, including **list** queries. The former is exactly the mounted
query set after a successful read turn. The latter indexes the windows of
its fresh answers: firing disarms a watch until its next read. It is not correct
to equate that fresh subset with all live subscriptions.

## Callback inventory

| Case | Android NativeActivity / Java | iOS UIKit | Headless twin | Before and change |
|---|---|---|---|---|
| Background/foreground | `onPause`, `onResume`; `onNativeWindowDestroyed/Created` independently | `applicationWillResignActive:`, `applicationDidBecomeActive:`; view layout/window loss | `background`, `foreground`, `surface`; C `!background`, `!foreground`, `!surface 0/1` | Previously Lean got no lifecycle events, Android blocked in `ba_lock`, and the runner kept ticking. New production `poll` works without drawing; sync is stopped/restarted, tasks and subscriptions torn down, camera and IME closed. iOS pauses its display link. Android detaches layers and makes frame locking nonblocking. |
| Surface lost during a frame | Native window callbacks hold the activity lock; layers detach under their lock | Main-queue commit checks foreground, window and viewport again | C twin aborts if a frame is submitted without an active surface | Android refuses a missing/paused window and rejects a frame whose size changed during layout. UIKit rejects a late commit and invalidates staging so the next frame is uploaded again. No frame waits indefinitely for a new surface. |
| Killed/restored | New `onCreate`; no `onSaveInstanceState` dependency | `didFinishLaunchingWithOptions:`; no `applicationWillTerminate:` dependency | Fresh `App.start` on the same DB; subprocess SIGKILL with writer paused | Previously start picked the first entry/home and lost drafts, page and scroll. Journal replay precedes community discovery, selection uses `switchToAcc`, and restore applies the checkpoint before first layout. `goneSeen` still comes from stored removals, so old removals are not announced. A missing/removed saved acceptance is never selected. |
| Rotation/resize | `onNativeWindowResized`, insets; orientation/density config changes remain in the activity | `viewDidLayoutSubviews`, safe area and keyboard guide | Mutable `Sim.viewport`, `.resize`; C `!resize W H` | Previously only height/insets changed in Lean; width and mounted layouts stayed old. All five viewport fields are read, every mounted row is laid out again, old paints/image sizes/page/chrome/sheet-grid caches invalidated, and the anchor corrects the offset. Portrait-only manifest/plist restrictions are removed. |
| Mount/unmount mid-sync | Serial Lean event loop plus writer/runner notices | Same | Actual incoming op committed after navigation; a captured old callback attempts read/paint/write | Previously hidden conversations still read/mounted/painted, and list watches survived pruning forever. Chat work now runs only on chat; leaving revokes leases, detaches the board, retires workers and drops the old tree. Arrivals update the store/root without resurrecting an unmounted page. Per-page sheet/peer/camera work is driven by active turns only. |
| Keyboard transitions | Insets animation, `nText`, `nSend`, `showIme`, main’s `setText` | Keyboard layout guide, text delegate, resign/become first responder, `setText` | Controllable text and IME; same-turn stale events | Previously native text was not restored and could overwrite a different page's draft. Navigation hides the old IME and sets the destination input; background clears height/composition. A lease rejects remaining input events belonging to the departed page. A height event delivered with a resize is retained for the same page, while stale touch coordinates are revoked. The final native edit is checkpointed even when its text event shares a poll with backgrounding. Keyboard opening is not restored at cold launch. |
| Cold/warm invite | `ACTION_VIEW` in `onCreate` and `onNewIntent`; `quiet` intent filter, `singleTask` | Launch URL and `application:openURL:options:`; registered `quiet` scheme | `Sim.urls`, `.deepLink`; C `QUIET_LINK`, `!link` | Previously neither shell delivered URLs. A production URL queue, separate from the debug channel, feeds `Community.Invite.parse` and `takeInvite`. A cold link with no identity opens Choose a name. A held community selects its acceptance without another join. Invalid links preserve selection. |

Lean Quiet implements only `quiet://join/…`; it has no message-link route or
message-link producer. Unsupported routes are rejected, not interpreted as
message ids. The supplied read-only `/home/holmes/libquiet` checkout has no
`app/src` directory in this environment, so it did not supply an additional
Svelte notification/message-link implementation to port.

## Geometry and anchors

The list is bottom-anchored. An anchor names a message plus the distance
from the viewport bottom to the message's top edge. After re-layout, the
offset is `Lifecycle.offset newTop above`; `resize_anchor` states that the
top edge stays exactly `above` pixels above the viewport bottom when that
offset fits in the content. At the content boundary the offset clamps to
zero. The same logical anchor is retained while it has this position,
even when a wide layout makes it short enough to sit wholly above the
viewport's bottom edge. This is not an
absolute screen coordinate: a rotation can remove that coordinate entirely.
At the newest end there is no anchor and offset zero remains pinned. If the
saved message is no longer readable, the fallback is the newest end. Layout
uses the same `Row.Layout` for painting and hit testing and does not retain a
bitmap made at the previous width.

The existing geometry laws quantify over **every** viewport, with the
existing `Geom.Fits` premise (header, composer and keyboard leave space).
`viewport_geometry` composes placement and page hit inversion for any such
size, not a fixed portrait size. A zero-height viewport contains no visible
list row; this work does not assert that arbitrary chrome can fit in an
arbitrarily small window. Native pixel placement remains the trusted seam.

## Exact new law statements

Types/names below are the declarations in the source, with their namespaces
shown. `M` is the running app's `StateT St IO`; `Checkpoint` is the serialized
local UI op. No theorem has `sorry` or additional axioms.

```lean
Lifecycle.unmounted_quiet {m : Type → Type} [Monad m] {α : Type}
  (s : Mount) (l : Lease) (action : m α) :
  owned s.unmount l action = pure none

Lifecycle.old_quiet {m : Type → Type} [Monad m] {α : Type}
  (s : Mount) (action : m α) :
  owned s.unmount.mount s.lease action = pure none

Lifecycle.subscriptions_exact (s : Mount) (k : ByteArray) :
  k ∈ s.subscriptions ↔ ∃ node ∈ s.tree, ∃ q ∈ node.2, (q.win default).key = k

Lifecycle.live_exact (l : Live) (s : Mount)
  (complete : ∀ q ∈ s.queries, l.entries[q]?.isSome = true) (q : Q) :
  (prune l s).entries[q]?.isSome = true ↔ q ∈ s.queries

Lifecycle.resize_anchor (top above : Nat) (fits : above ≤ top) :
  (top : Int) - offset top above = above

Lifecycle.restore_checkpoint (s : Checkpoint) :
  restore (Codec.encode s) = some s

Lifecycle.mounted_runs (n : Nat) :
  owned (m := Id) ({ generation := n } : Mount) ⟨n⟩ (pure 7) = some 7

App.page_round (p : PageId) : PageId.ofCode p.code = p

LifecycleLaws.unmount_read (s : St) (q : Q) :
  (App.read q).run (unmountState s) = pure (default, unmountState s)

LifecycleLaws.unmount_write (s : St) (w : Community.Write) :
  (App.writeAll w).run (unmountState s) = pure (false, unmountState s)

LifecycleLaws.old_callback (s : St) (action : M α) :
  (App.owned s.life.lease action).run
    { unmountState s with life := s.life.unmount.mount } =
  pure (none, { unmountState s with life := s.life.unmount.mount })

LifecycleLaws.restore_page_anchor (s : St) :
  (Lifecycle.restore (Codec.encode (checkpoint s))).map (fun cp =>
    (PageId.ofCode cp.2.1, cp.2.2.2.1, cp.2.2.2.2.1)) =
  some (s.page, (s.mark.getD (.empty, 0)).1, (s.mark.getD (.empty, 0)).2)

LifecycleLaws.apply_page_anchor (s target : St)
  (valid : ∀ x off, s.mark = some (x, off) → x.isEmpty = false) :
  (applyCheckpoint target (checkpoint s)).page = s.page ∧
  (applyCheckpoint target (checkpoint s)).mark = s.mark

LifecycleLaws.viewport_geometry (g : Geometry.Geom) (fits : g.Fits)
  (over bf bn r y : Nat) :
  Geometry.Seam.place g over bf bn r =
    Geometry.Seam.home g bn (Geometry.Seam.frameRow g over bf r) ∧
  Geometry.Seam.tapRow g y = (y : Int) - g.top

LifecycleLaws.viewport_possible :
  (Geometry.Geom.mk 1280 24 300 80 100).Fits
```

`mounted_runs` and `viewport_possible` are formal non-vacuity witnesses.
The runtime suite also checks a real, nonempty message anchor and a nonempty
mounted cache satisfying `live_exact`'s completeness premise.

## Port from fe7b66f

The types were extracted mechanically from **today's** App.lean into
AppTypes.lean; no old St replaced the current one. AppLife.lean needs those
types without importing the root that calls its hooks. The existing reader,
window, picture retry, boot task, secure randomness and page code remain.

Main's `anchor : Option Pos` still chooses a bounded conversation window.
The durable UI position is now `mark : Option (Id × Nat)`, so the two anchors
have different jobs. Checkpoints also retain the marked message's Pos, and
restore requests a bounded reader window around it. They do not load all
conversation rows. The UI mark is retained until the dedicated reader
publishes the requested window, including when that completed window is
unchanged. A completed window without the mark resolves to the newest end. The law statements above therefore use `mark` where
fe7b66f used `anchor`. The page codec includes today's duplicate page.

Reader.Worker owns a cancellable dedicated reader. Unmount signals it,
replaces the page's Shared refs while retaining the writer's commit counter, and retires the
worker. Reaping its completed result recovers the connection. It resets the inline reader cache too. Navigation and background
also clear picWants, retryWants, lastSlices, imgRetry and image tasks. Resume
starts a fresh reader for the mounted conversation. Every reader pass prunes
its cache against its current dependency tree, including list queries.
The root's live tree and the reader's want/dependency tree have separate
caches; both call Lifecycle.prune.

Suspend starts a dedicated stopNodes worker that retains netBoot and
stops its eventual runner. It polls the worker only until its deadline;
foreground cannot start another runner until that handle completes.
App.submit now journals store-owned writes and uses the runner's trySend
channel. Failed offers stay in toNode in order. Suspension preserves them
and offers nothing; foreground re-offers them to the new runner. A revoked
page still cannot call writeAll (unmount_write). A store-owned submit while
suspended is allowed, durable and parked; it is not an old page callback.
Checkpoints are committed on the writer's connection and thread, never
the frame's.
Ordinary input still runs inside that transaction. Lifecycle barriers run
outside it, and suspension reads the native field before hiding it so the
last edit in the same poll is not lost.

Runner.stop explicitly closes its listener after joining the acceptor. The
Lean 4.34 runtime has no close API for UV sockets, so engine/native/listener.h
invokes the external object's UV-close destructor once and replaces it with
a no-op destructor. Retained Runner references do not retain the listening
port; repeated stop cannot close a reused descriptor. This ABI-specific
native seam may only be called after the sole acceptor joins. The real TCP
regression retains the old runner and starts two successors on its port.
A native destructor observation also tests the actual Runner.stop without
needing an OS socket, including its negative control.

IO.Process.exit 0 after Main's loop is retained, fixing the scripted host's
hang on the perpetual local writer. Lifecycle's BEq instances are local,
reusing LiveLaws; existing law statements and Message.read order are kept.

## Verification

The named `host:lifecycle` task builds app_lifecycle and quiet_host and runs
the scenario, SIGKILL and production C twin drivers. It is wired into
`tests/app/run.sh`. `engine:restart` builds and runs runner_restart, and is
in `tests/engine/run.sh`. Both are non-RELEASE tests. The whole gate is
`ci/local.sh check engine app readme reorg`; this sandbox uses SKIP_TCP=1,
which still builds the real TCP executables for the lead to run outside.

Initial port validation (2026-10-28, before the resume correction below):

- The axiom audit passes all **582** laws (567 existing, 15 ported), with
  standard axioms only. Existing law statements remain unchanged.
- The lifecycle scenario passes **91** assertions in this TCP-denied
  sandbox. It covers all 72 checks retained from fe7b66f and adds reader
  teardown/restart, picture cleanup, ordered parked writes, write-producer
  draining, asynchronous anchor resolution and the last native text edit.
- The process test sends **one SIGKILL** to its recorded child PID, then
  runs **two cold restores, four assertions each**, including exactly-once
  replay and a nonempty message anchor.
- The production C twin exercises **three state checks, two suspensions,
  two resizes, and two invite deliveries** (cold and warm). Its native seam
  rejects any frame submitted without an active surface.
- The runner close test has **two local assertions**: stop explicitly
  closes a listener still held through a Runner, and repeated stop closes
  it once. The real TCP test adds **three assertions**, including two
  same-port restarts while an old Runner remains referenced; those need a
  host that permits TCP.
- **35 lifecycle negative controls** are rejected and reverted. The first
  24 from fe7b66f remain; the added controls remove the reader barrier,
  retain reader cache/picture requests, lose parked/producer ops, reverse
  parked order, retain the listener, remove missing-anchor fallback,
  ignore unchanged reader windows, discard an anchor before its board
  arrives, and omit the final native edit. Each executable mutant built
  before its expected runtime assertion failed; proof mutants failed to
  prove the original statement. Sources were restored and rebuilt.
- Android: **five C translation units** pass NDK syntax checking (including
  the SQLite/explicit-close glue), and the Java activity compiles against
  Android 35 with Java 17. These are non-RELEASE checks with LQ_CTL enabled.

`SKIP_TCP=1 ci/local.sh check engine app readme reorg` passes all five
parts: check (3 s), engine (630 s), app (123 s), readme (18 s), reorg (5 s).
The engine reports **129,302 passing assertions**, including the two local
listener assertions, plus **29 rejected hardening controls**. The app gate
reports **111 existing scenario assertions** (including all 22 inkless
font glyphs), the lifecycle/crash/C twin results above, and **two rejected
picture-retry controls**. The README checker validates **354 links** and
its own negative controls; reorg rewrites **166 files, zero wrong**.
The named `mise run check` also passes all 582 laws; `mise run host:cross`
and `mise run host:attach` both build successfully and explicitly skip
TCP execution under SKIP_TCP=1. These skips are not runtime passes.

The initial scratch baselines caught omitted new files; tests/snapshot.sh now includes
the listener header/fixture, and the picture retry snapshot includes
AppTypes.lean and AppLife.lean. README links/counts are regenerated by the
existing wiring checker; no model law is newly labelled as running code.

Initial remaining verification was TCP, an iOS SDK build, and native OS
callback/camera/keyboard behavior on Android and iOS. The lead has since
passed the engine gate with TCP (684 s), including same-port rebind. The
app TCP scenarios still require the lead's rerun after the correction below.
No phones, emulators or Mac were used. SQLite power-loss durability and
the native close ABI are not Lean proofs. The append-only local UI journal
still needs a retention policy. No build hit the memory cap.

All mutations are restored and the inclusive patch is saved to
out/lifecycle-port.patch after each finished piece.

The agent could not commit: Git could not create
`/mnt/storage/holmes-wt/lq/.git/worktrees/lq-lifecycle-port/index.lock`
(read-only filesystem). No commit hash was produced; the work remains on
`a3/lifecycle-port`, based on `14a2728`. The complete patch and the requested
commit message (with the Codex co-author footer) are in
`out/lifecycle-port.patch` and `out/lifecycle-port-commit-message.txt`.

## Resume correction: the lead's TCP failure

The reported `A 0, B 31, before 1` was a stale Home count, not lost chaos
writes: B already had the original message plus all 30 new messages.
The non-TCP reproduction uses the actual Runner.runLoop and Node.onWrite
on SQLite. It holds netBoot pending and then fills a one-slot channel.
Before the fix, six checks passed (including the store's 31 messages) and
only Home's total failed. The test also checks every parked op byte for
byte in the node's store. refreshHomeCount now owns a count-only readable
query (limit zero); the hidden conversation stays unmounted. No Message.read
bind order or existing law statement changed.

The named host:lifecycle-node test now has 28 assertions: the eight count,
boot and backpressure checks, plus deadline, revocation and replacement-node
checks. It deliberately delays cleanup for 400 ms while calling suspend
with a 150 ms budget, and checks return by that deadline. It verifies that
late producer ops enter the on-disk checkpoint after their mapped futures settle,
and that foreground writes
remain parked until the old runner finishes and the replacement accepts
them in order. A cancellation during an actual Reader.pass allows one
query, denies subsequent queries, and publishes nothing.

App.suspend defaults to one 250 ms absolute deadline. waitFor polls with a
1 ms sleep, reserving the final 5 ms polling margin. On expiry the app owns
netStop, readerStop, paintStop and chaos; background polls reap finished
work, and foreground only polls without joining. Native SQLite/OS calls and OS scheduling
are still the platform seam; this is a tested deadline for task/queue
waiting, not a hard real-time theorem about the OS. Shutdown can remain
pending after timeout. No second node or parked-write offer is allowed
while the old node is stopping.

The block-rule changes from ca4d713 are ported separately into Wiring.
`bounded App.suspend ...` is the only permitted exception. It permits
waitFor, but the checker still rejects an unbounded IO.wait or blocking
send inside suspend (outside its named dedicated threads). Ordinary frame,
navigation, resize and resume paths cannot reach those calls or waitFor.
The new negative-control task mutates the count, timeout, retained handles,
reader guards, pending-stop offers and the exemption/block rules; it is
wired into the app gate along with the positive task.

The lead's original TCP failure and passing engine log are preserved in
out/lifecycle-lead-app-failure.log and out/lifecycle-lead-engine.log.
Validation of the correction (2026-10-28):

- The named `mise run check` passes all **582 laws**, including the same
  **15 lifecycle laws** above. No existing statement or axiom changed.
- The requested gate's check (2 s), engine (603 s), readme (18 s) and reorg
  (5 s) passed. Its first app run exposed a race in the new test: waiting
  for the producer did not wait for the separately scheduled mapped
  future. The test now polls the app-owned handles before checking the
  checkpoint. The corrected app gate passes in **384 s**. The final readme
  rerun passes in **19 s**, validating **354 links** and the block rule.
- The required named `host:cross` and `host:attach` tasks each build
  successfully and explicitly skip TCP execution here (20 s each).
- Engine: **129,302 assertions**, **29 rejected hardening controls**, and
  both local listener-close checks pass. The lead separately passed the
  engine's real TCP gate, including same-port restart (684 s).
- App: **111 existing scenario assertions**, **91 lifecycle assertions**,
  **28 actual-node/deadline assertions**, **two picture-retry controls**,
  the SIGKILL/two restores, and the production C twin checks pass.
- **13 new negative controls** are rejected: remove Home's count update;
  remove the deadline; drop the stop handle; leave a late boot running;
  read after revocation; publish after revocation; offer while stopping;
  join an unfinished stop; drop the reader handle; omit the exemption;
  widen the exemption to resume; block resume; block suspend outside
  waitFor. Each runtime mutant builds and fails its named assertion;
  each wiring mutant builds and fails the intended reachability check.
  All mutations are reverted and the positive **28-assertion** suite
  passes again. Logs are in out/lifecycle-node/negative/.
- The prior **35 lifecycle controls** remain; their mutation targets are
  updated for retirement and the pending-stop guard. They were run during
  the initial port; this correction reruns the scenario and new controls,
  not those 35 controls again.

The scripts run one build at a time; no build hit the memory cap. All
local gates use SKIP_TCP=1 and build the TCP executables. The lead must
rerun net_join, cross and attach outside the sandbox; this correction does
not claim a real TCP app pass. No devices or Mac were used. Logs for this
correction are out/lifecycle-resume-*.log and out/ci/*.log.

The final commit attempt also failed to create the worktree index lock
because the shared Git metadata is read-only. No commit was made. The
updated commit message and inclusive patch are saved at the paths above.


## Re-port onto d83c386

This worktree is a3/lifecycle-port2. It re-applies b1769e6's behavior to
main d83c386; the prior sections' build logs, counts and commit limitation
are historical. The current patch and requested commit message are
out/lifecycle-port2.patch and out/lifecycle-port2-commit-message.txt.

AppTypes is extracted from today's app, including PageId.DecidableEq,
PageId.all, native, touched, and toNode as an array of write batches. The
proved openSt, backSt, switchSt and textInto functions keep their behavior
and law statements. St.withNav moves beside the types; checkpoint restore
replays the decoded stack through Nav.go, so a page restore cannot bypass
Nav's no-duplicate rule. The navigation source audit covers both new files.

App.frame retains main's netted filings/verdicts, flushNode, takeDone and
syncText. The mounted conversation retains separate window/count reads,
Want.withView and Want.ofFrame ordering, and picture retry wants. Other
pages request their own lists; no hidden conversation rows are requested.
The reader now serves every mounted page, including Home. Root cache
pruning still uses live.keep with touched before the lifecycle tree's exact
prune; the reader retains main's reverse index and rest optimization.
The exact subscription test also checks each indexed window against its
cached answer, through today's Live.subs. subscriptions_exact expresses
its key projection as (q.win default).key, replacing the removed Q.watch
API. The other 14 lifecycle statements are unchanged from b1769e6.

Only Io.setText / lq_set_text restores native input. Main's into_target
and into_native laws remain unchanged. Io's positional default and both
shipping entry points use this field order. Platform has 18 externs:
main's 16 plus lq_poll and lq_links. The Linux shell supplies empty poll
and URL queues; its existing desktop event pump still drives App.step.
Linux OS background/deep-link dispatch is not added by this port.

Reader actions are now part of teardown too. Unstarted page intents are
revoked; a pass checks revocation before querying, before judging an
intent, after judging and before publishing. An act already judged and
handed off as a write belongs to the store: parkDone checkpoints and parks
it without invoking its page continuation. A detached board is retained
until its reader finishes, so an already-accepted late hand-off is not
lost. A replacement board retains pending outbox rows and the writer's
commit counter; it never inherits stale page subscriptions.

Batched parked writes keep their submission order through main's
NodeOffer.offerList. They are not offered during suspension or pending
teardown. The 250 ms deadline and explicit listener close remain. Wiring
retains main's submitWaits control, admits only the named App.suspend
bounded exemption, and still rejects an unbounded join inside it.

The adapted node suite has 32 assertions: the prior 28 plus four reader
act checks (judged hand-off, durable parking, delivery after resume, and
in-flight revocation). Its negative suite has 16 mutations: the prior 13
plus dropping an accepted act, accepting a revoked act, and bypassing
the desktop anchor hook. Desktop.resize now calls App.resize before its
existing settleFrame path. Eight new desktop assertions check a nonempty
scroll anchor and its identity/position through seven resizes. The original
35 lifecycle controls retain their mutations, updated to the new APIs.
No phone, emulator, Mac or network fetch was used. Other worktrees were
read-only references.
Current validation:

- The named mise check passes **699 laws**, including all 15 lifecycle
  laws, and the expanded navigation audit passes. It was run again after
  the final desktop hook and legacy controls.
- The app gate passes in **536 s**: **105 desktop checks / 27 renders**
  (including eight added anchor assertions), **91 lifecycle assertions**,
  **32 node/deadline/action assertions**, one SIGKILL and two four-check
  restores, and the production C twin's lifecycle/resize/link script.
  Main's bidi, node queue, two-node, attachment arrival, navigation and
  picture-retry suites are retained. The Linux binary builds; local X
  execution is explicitly skipped in this sandbox.
- All **16 node/deadline/desktop controls** are rejected, source restored,
  and the 32-assertion positive suite passes again. Main's five navigation
  controls and two picture-retry controls also fail as intended.
- **Eight affected legacy lifecycle controls** are rerun and rejected:
  lose-subscriptions, save-wrong-page, apply-wrong-anchor,
  lose-native-draft, drop-parked-writes, lose-producer-writes,
  reverse-parked-order and retain-reader-cache. The other 27 controls
  remain, with their prior run recorded above; they were not rerun here.
- Android: **five C units** pass NDK syntax checking with LQ_CTL enabled;
  the Java activity compiles with Java 17 against Android 36. No device
  was installed or run. iOS still needs an SDK build and OS verification.
- The first gate passed check and reorg; engine's tests and 29 controls
  passed but its final new restart script lacked its executable bit.
  The port now preserves all executable modes from b1769e6. README links
  also needed regeneration after the final edits. Both parts are rerun
  after those corrections: engine passes in **627 s** with **129,313
  assertions**, **29 hardening controls**, and the two explicit listener
  close checks; readme passes in **20 s** with **416 links** and its
  entry/door/block checks and controls. Reorg passes in **4 s**. All five
  requested parts are green. No build hit the memory cap.
- Named host:cross and host:attach each build successfully (20 s each)
  and explicitly skip TCP execution. These are build passes, not TCP
  runtime passes. The desktop also audits **nine laws** on standard
  axioms. Bidi retains **73,599 in-scope Unicode cases**, **40 regression
  checks**, and **nine headless checks**, all passing.

The remaining real TCP runs (including same-port restart, net_join, cross
and attach) belong to the lead outside this sandbox. Native OS lifecycle,
keyboard and camera delivery remain unverified on devices. SQLite's native
crash/power-loss seam and the local journal's retention policy are still
as described above. Logs for this re-port are out/port2-*.log and out/ci/.


Final commit status: git add failed to create
/mnt/storage/holmes-wt/lq/.git/worktrees/lq-lifecycle-port2/index.lock
because the shared Git metadata is read-only. No commit hash was produced.
All completed changes remain on a3/lifecycle-port2 at base d83c386.
The inclusive patch and commit message with the required co-author footer
are saved in out/lifecycle-port2.patch and
out/lifecycle-port2-commit-message.txt. No push was attempted.
