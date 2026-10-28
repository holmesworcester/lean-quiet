# Performance

What each step of the app and the node costs, proven over the code that
runs, as a function of the configuration (`Budget`) and never of how
much the community holds, except where a row below says so and names
its fix. A phone k times slower multiplies each bound's time by k; the
bounds do not move.

docs/BOUNDS.md (holmes-a3's) is the node's and sync's inventory; this
file holds the cost model both use, the app's steps, the O(N) table, and
the argument that the UI and the node always make progress.

## The cost model

### Doors and the meter

Code whose cost matters is written once, over a monad, and does its
costly work only through doors: a store read, a list, a write, a hash,
a task spawned, a pass over a list, a byte string copied. Each door
charges the meter (`tick`, engine/core/Cost.lean) for what it does.

- **Where code runs** (`Id`, `SqlM`, `Model`, `HeldM`), `Tick` is
  `Tick.free`: a tick is `pure ()`, and the code compiles to what it was
  before the doors.
- **Where code is measured**, the same code runs in `CostT m`, a writer
  over m: each action returns what it charged beside its value, and no
  action can read the meter, so what code computes cannot depend on what
  it was charged. `Counted` is `CostT Id`, for pure code; `CostT m` over
  a store's monad counts what a node does to its store
  (engine/core/CostStore.lean: every `Store`, `Lists`, `Turn` and
  `Fresh` door, charged).
- **`Valued`** (`Id` and `Counted`): a value that binds compose and
  ticks leave alone, so a counted function is proven once to compute its
  spec, and its cost law is about the code that runs.

### Units

| field | one unit is | charged by | time (`Units`) |
|---|---|---|---|
| `reads` | a point read: an op, a status, a waiter list | the store's doors | `read` |
| `lists` | a list query (`Lists.list`) | the list door | `list` |
| `writes` | a row written, or an op of a write turn | the store's doors | `write` |
| `seeks` | a B-tree descent in SQLite | the store's doors, by SQLite's plan (below) | `page · levels N` |
| `rows` | a row stepped over after a seek | the list, waiter and lookup doors | `row` |
| `hashes` | a call to the hash | `hashM` | `hash` |
| `hashed` | a byte given to the hash | `hashM` | `hashByte` |
| `work` | a list cell passed, a word operation | `pass`, the codec's digit doors | `cell` |
| `copied` | a byte encoded, decoded or copied in bulk | the codec's byte doors | `byte` |
| `spawns` | a task spawned | `Pics.spawn` and every spawn door | `spawn` |

`Meter.time U N c` weighs a meter by the units on a store of N rows. It
is linear, so it is a `Field` like any count, and a budget proven for
every field is a time bound on every phone (`Costs.time`). The units are
measured per phone, not proven; the laws are about the counts.

### The SQLite assumption

`levels N = log₂ N + 1`: a seek into a table or index of N rows visits
at most that many pages, because every page of SQLite's B-trees but the
root holds at least two entries; a row after the seek, in index order,
is the next entry of the same or the next leaf page. This is SQLite's
file format, assumed and not proven. What each door costs SQLite is a
table in engine/core/CostStore.lean, from the statements in
engine/core/Sqlite.lean and Query.lean (`listCost` for a list: three
seeks, one per row for its verdict, and its rows and range count).

### The bound template

A law is `Costs B x`: x costs at most the meter B in every field, and so
in time. B is built from the inputs and the `Budget`; x is the code that
runs, counted. The rules are one per way code is put together:

| code | rule |
|---|---|
| `pure a` | `costs_pure`: 0 |
| a door, `charged c y` | `costs_charged`: c |
| a door charged by its value, whose values all have P (`Sat P y`, an assumption about the store) | `costs_bindP` |
| `x >>= f` | `costs_bind`: A + B, or `costs_bind_le` into a given C |
| `if c then x else y` | `costs_ite` |
| a recursion on a list or a fuel | induction, a door per step |
| a bound too tight | `Costs.mono`, by `meter_le` (kind by kind, `omega`) |

Do-notation's join points (`have __do_jp := …; match …`) come apart
with `dsimp only` before `split` or `cases`.

Each law comes with a **mutant control**: the old code, or the obvious
wrong one, run in tests/engine/CostCheck.lean on real inputs, computes
the same and is over the budget.

### A worked example: judging an op

`Engine.step` (engine/core/Core.lean) pops an op, reads its status and
the op, reads the statuses of its requirements, and either decides it
(files its fact, wakes its waiters) or waits on what is undecided.
engine/core/IngestCost.lean proves, over every store:

```lean
theorem step_costs (fam : Family F) {R K W : Nat} (hK : ∀ x f, (fam.fileKeys x f).length ≤ K)
    (hR : ∀ x, Sat (ReqsLe R) (Store.getOp (F := F) (m := m) x))
    (hW : ∀ x, Sat (WaitersLe W) (Store.waiters (F := F) (m := m) x)) :
    Costs { reads := 4 + 2 * R, writes := 3 + K + W + R, seeks := 7 + 3 * R + 2 * K + W, rows := W }
      (step (F := F) (m := CostT m) fam)
```

The proof follows the code: the pop's charge, then `cases` on what it
returned; the status read; the op read through `costs_bindP`, which
hands the rest of the proof `o.reqs.length ≤ R`; `statuses_costs` (a
read per requirement, by induction); then `dsimp only` and `split` on
the verdict, into `decide_costs` or `waitOn_costs`. Each step's bound is
added with `costs_bind_le` and closed by `meter_le`.

What it says: judging an op costs O(R + K + W) store work and nothing
proportional to the store but the seeks' `levels N`. At R = 6, K = 4,
W = 0 and N = 10⁶ rows, that is 33 seeks, 660 page visits. W is the
fan-in burst: an op that n ops arrived before wakes all n in one step
(costcheck: 40 early ops, one step, rows = 40). The mutant control
re-reads every requirement's status for each one (`waitOnSlow`): over
`waitOn_costs` at every size.

### The `Budget` and the inventory

a3's `Budget` (engine/wire/Bounds.lean on a3/bounds) holds every
constant a bound names, with what runs as its defaults. A law over it is
`theorem step_cost (B : Budget) … : Costs (meter in B's fields) (stepM B.sync …)`,
and `Costs.time` turns it into time. The fields the laws in this file
need beyond a3's: `drain` (the capped write turn's), `reqs` (an op's
requirements, capped at intake: today only the frame bounds them, at
about 32 000), `refill` (the reader's refills per pass), `inflight` (the
picture decodes in flight), `rowMin` (the shortest row, in pixels, which
bounds the rows on screen).

An inventory row is `| step | bound | theorem | status |`, the status
✅ proven, 🟡 proven of a model the code is not yet shown to run, 📏 a cap
the code checks and measured, ❌ grows with the store and names its fix.
`ci/inventory.py` (in tests/check.sh) fails when a ✅ or 🟡 row names a
theorem the axiom audit does not list, or a ❌ row names no fix; its
negative control is a table that breaks both rules.

## The app's frame (the Live change signal)

The frame never reads the store. A reader on its own thread (dedicated,
its own connection, one read transaction per pass) owns the journal's
cursor, the live cache of list answers, the outbox, and every view's
evaluation. It publishes each value the frame wants to a `Board`
(engine/renderer/Board.lean), versioned: a refill whose value is equal
keeps its version, and a different one takes the next version of one
counter and is marked moved. The frame takes the moved set with one
atomic swap and works only on the values in it that are on screen.

The signal is the effect (a value moved) at the moment it lands, not its
cause (a commit's notice): with refills off the frame, the two land in
different frames, and a frame gated on notices misses the refill that
lands after its notice was taken (holmes-1e's TwoNodes failures).

The board's operations are the code the reader and the frame call; the
world (`Live.World`, engine/renderer/BoardLaws.lean) is a model of the
threads around it whose steps are those operations: the writer's
commits, the reader's passes, the frame, in any order. Its store is
abstract, and the one thing assumed of it is the engine's `view_stable`
(`World.Stable`: a commit that touches no list a value read leaves it).

| step | bound | theorem | status |
|---|---|---|---|
| a refill | equal: nothing changes; different or new: the next version, moved | `put_same`, `put_moves` | ✅ |
| a version | one value, along any run of puts, takes and keeps | `ver_ident`, `Step.fresh` | ✅ |
| between two takes | no change lost: every value held is moved or shown | `seen_put`, `seen_take`, `seen_keep` | ✅ |
| any interleaving | every value held is dirty, touched by a commit not taken, or the store's; and seen | `inv_commit`, `inv_pass`, `inv_frame` | ✅ |
| no missed update | a pass refilling every marked want, then a frame: every want shows the store's value | `settle` | ✅ |
| settling time | passes of `refill` each: ⌈marked / refill⌉ of them, then a frame | `marked_pass`, `settle_passes` | ✅ |
| the mutant | a frame gated on notices shows 0 for ever where the store holds 1; this frame shows 1 | `gated_stale`, `ungated_fresh` | ✅ |
| a user's action (holmes-1e's (a) and (c)) | run before any refill; its value (pending op or refusal, `Val.done`) and every want it touched shown one frame after the one pass that judged it, however long the backlog; none left queued. The latency given up: one bounded pass and one frame, where it showed in the composing frame | `acts_shown`, `passActs_acts` | ✅ |
| the composer (holmes-1e's (b)) | the frame's alone: no reader step changes it or depends on it; typing changes nothing else | `passActs_comp`, `passActs_indep`, `type_only` | ✅ |
| a commit's stability | asked of each commit as made (`StableAt`), as window-subs' `notice_iff` gives it | `inv_commit` | ✅ |
| the reader's pass as it runs (`RWorld`: Live's stale reads, each want's reads, mark then pick, as Reader.pass does with `Live.mark` and `Live.pick`) | every step keeps the invariant; a pass reading every marked want, then a frame, shows the store's values | `RWorld.inv_pass`, `RWorld.inv_commit`, `RWorld.inv_evict`, `RWorld.settle` | ✅ of the decisions Reader.pass calls (the diff that makes it call them is with the lead); its reads are the moment's by holmes-1e's LiveLaws |
| a pass's decisions | the marked set a hash set: marking and picking a step per want, O(wants); as a list (the mutant) a pass over it per want, 40,000 steps for 200 dirty wants | `markM_cost`, `pickM_cost`, `mem_mark`, `pick_eq`, `mem_eraseAll` | ✅ |
| the mutant: staleness checked while reading (holmes-1e's first pass) | two wants sharing a read: the first read refreshes it, the second shows 0 for ever where the store holds 1; marking first shows 1 | `eager_stale`, `marked_fresh` | ✅ |
| the frame's reads | none: no store read, no list, no SQL, decrypt or decode but through `Pics.spawn` | `frame_reads` (Doors over App.step) | ❌ the frame reads SQLite today (readView, slicesOf); fix: the reader above |
| the frame's work | a + b · rows on screen + the moved values' sizes | `frame_work` | ❌ `bottoms` and the mount and paint loops walk every loaded row; fix: a prefix-sum tree over heights and a binary search for the window |
| an unchanged frame | nothing moved, no event, no scroll, no paint finished: no work, the same rows | `frame_idle` | ❌ every frame re-runs the views through the cache; fix: the moved set |

## The hot paths, in N

N is the community's size: its ops, members, or rows under one key,
whichever the row names. Each bound is over the code that runs, counted
with the meter above.

| step | bound | theorem | status |
|---|---|---|---|
| ingest one op | 1 read, ≤ 2 writes, 3 seeks | `ingest_costs` | ✅ |
| judge one op (validate, file, wake) | ≤ 4 + 2R reads, 3 + R + K + W writes, 7 + 3R + 2K + W seeks: R requirements, K keys, W woken | `step_costs`, `decide_costs`, `waitOn_costs` | ✅ for R, K and W given; W is the fan-in, below |
| the intake cap | an op citing more than `maxReqs` = 64 requirements is refused at intake, a peer's or this node's own, bare or in a job; every op a node stores is within it, so R = 64: at most 132 reads a step. Without the cap (the mutant) a 200-requirement op is stored and its step reads 403 | `intake_reqs`, `intakeConn_reqs`, `stored_capped`, `fed_reqs`, `step_capped`, `step_reads_fed` (at every state a node fed through intake reaches, on the counted run itself) | ✅ |
| a list read | ≤ limit + cap rows and 3 + limit seeks, on any store whose answers fit; the model's do, and SQLite's are the model's (querydiff) | `list_costs`, `model_fits` | ✅ for lists with a limit and a count cap |
| a view | one list door per list it reads | `view_lists` | ✅ |
| the frame's values | settle in ⌈marked / refill⌉ reader passes and one frame | `settle_passes` | ✅ of the board the reader and frame are to call; 1e is wiring it |
| a sync round | ≤ 2k + 3 messages, ≤ 1 + fan·(2k + 2)·Δ claims; cold answers O(fan · N log N) until the treap is on the running path | docs/BOUNDS.md | a3's |
| per-tick node work | the dial hook, then per session: its rooms (`trusts` per established pair), the walk (≤ `walk` steps, 2 reads each), a round; then `react` | the walk's `walk_reads`, `tick_reads` (patch sent for a3/bounds) and a3's round rows | 📏 O(sessions × rooms) given each family hook is bounded; `react` is not, below |
| key wraps per approval | one wrap, to the new member's device; at most three ops in all, whatever the community holds; wrapping to every member (the mutant) makes four at three members | `approveReq_ops`, `wrapAll_over` | ✅ |

## Every step that grows with N

| step | grows with | theorem | status |
|---|---|---|---|
| the frame reads SQLite (`readView`, `slicesOf`): a slow read is a slow frame | the lists on screen and their rows | `frame_reads` | ❌ fix: the reader and the board (above) |
| `bottoms`, the mount and paint loops, `findIdx?` | loaded rows: every row from the newest to the window, each frame | `frame_work` | ❌ fix: the rows' heights tree (below), which App is yet to call |
| the rows' heights tree (engine/renderer/Heights.lean): the row at an offset, where a row starts, a height set, a row pushed | log₂ rows: at most the tree's depth d, 2^(d-1) < rows; 13 steps at 5,000 rows, where the walk takes 4,981 | `find_spec`, `start_eq`, `set_toList`, `push_ok`, `rows_cost` | ✅ of the structure |
| the window by binary search | the rows offsets [lo, hi] overlap are those from `find lo` to `find hi`; rows below end at or under lo, rows above start over hi | `start_mono`, `below_window`, `above_window` | ✅ |
| both ends (new messages below, older pages above an origin) | the row at an offset, on either side, in one find | `Both.rowAt_spec` | ✅ |
| a window's rows, rebuilt (a late message lands mid-window; a removed one keeps its slot at height 0) | one node per leaf and pair: at most 4 · rows + 1 steps, O(window), the tree what it must be | `rebuild_ok`, `rebuild_cost` | ✅ |
| the window | at most above + below rows: its two reads, each within its limit (`Fits`) | `window_rows`, `list_costs` | ✅ |
| the anchor | when the estimate below the window changes by Δ, moving the offset by Δ leaves every window row where it was on screen | `anchor_stable` | ✅ |
| the conversation's re-read | `limit`, which grows as the list scrolls up | `list_costs` | ❌ fix: a window of rows around the anchor, read by `after`/`before` |
| range counts with `cap = 0` (every list the app reads) | the rows in range | `list_costs` (needs `0 < cap`) | ❌ fix: a3's capped counts ("999+") |
| `present`, `members`, `recipients` (`admission.all.read [c]`, then `live` reads each admission's removals) | members: O(members) lists per re-read | `view_lists` | ❌ fix (after fd/removal, over its Live/Cut): the people list read by window on the reader, cut entries skipped, a capped count in the header; laws stated as `present_window_stmt`, `present_window_cost_stmt`, `present_count_stmt` (ops/app/Plans.lean) |
| `decide` wakes every waiter at once | an op's fan-in: n ops that arrived before it, in one step | `decide_costs` (W) | ❌ fix: push the decided id once, and let pops wake its waiters at most `drain` at a time |
| an invitation's threshold over 62 | its admission would cite more than `maxReqs` and be refused at intake | `invite_threshold`, `check_invitation` | ✅ fixed: the invitation's validator refuses a threshold over maxReqs − 2 (62), and `approveReq` composes no admission past it |
| every op this node authors (holmes-a3's check) | a constant per writer, none growing with the community: Community's writers cite at most 4, an admission 2 + its threshold (≤ 62); the Connection family's at most 4 | `*_reqs`, `found_authored`, `inviteTo_authored`, `joinOps_authored`, `approveReq_authored`, `rename_authored`, `removeMember_authored`, `introduce_authored`, `receiptFor_authored`, `join_authored`, `send_authored`, `writers_le` | ✅ |
| sync's have and want (up to `maxIds` ids as requirements) | never reach intake: a session's bytes are stored only as ops of no wire kind; the bare path keeps only conn ops, and a wire op is never one | `recv_takes_no_wire`, `wire_not_conn`, `intakeConn_wire` | ✅ |
| an op's requirements | was bounded only by the frame (about 32 000) | `stored_capped`, `step_capped` | ✅ fixed: the intake cap, `maxReqs` = 64 (a3's `Budget.reqs`) |
| `react` | `opened.all`, `request.byTo` and a count per request, every entry point | none | ❌ fix (after fd/removal): react driven by the turn's new ids, a capped sweep on the clock; laws stated as `react_reads_stmt`, `react_sound_stmt`, `react_live_stmt`, mutant `react_scans_stmt` (ops/app/Plans.lean) |
| the runner's event channel | unbounded: a peer sending faster than the node handles grows memory | none | ❌ fix: a bounded channel per socket, its reader waiting on its own thread, so TCP pushes back |
| the write turn, boot, purge, cold rounds | the store | docs/BOUNDS.md | a3's |

## Large communities: open questions

These are for a decision, not decided here.

- **Sessions.** Every member dials every member it trusts, so a node
  holds O(members) sessions and each tick costs O(sessions × rooms). A
  bounded-degree overlay (each node keeps at most D sessions, chosen so
  the graph stays connected with small diameter) makes a tick O(D ×
  rooms), and delivery takes at most diameter × round time. Which graph,
  who picks the neighbours, and how a removal reshapes it?
- **Membership reads.** `present` is O(members) per change. A present
  set kept as ops (an admission filed under a present key, a removal
  filing it out) makes it a windowed list. Is a people list ever read
  whole?
- **Keys.** With no rotation, an approval wraps one key: O(1). Rotating
  on removal would wrap to every remaining member, O(members) ops per
  removal; a tree of keys (TreeKEM-like) makes it O(log members).
  Is rotation wanted, and when?
- **Fan-in.** A popular op (the community's root, a pinned message) can
  have every op wait on it while it is missing. Wake in chunks, or
  require the root before anything else syncs?
- **Pending requests.** Join requests to an admin grow with the
  community's openness: cap, expire, or page them?

## Progress: the UI never starves, the node always moves

### Threads

| thread | runs | waits on |
|---|---|---|
| UI main (Java, UIKit) | input, insets, the activity's life | nothing of Lean's: events go into a buffer Lean drains each frame |
| compositor (AChoreographer, CADisplayLink) | at every vsync: the scroller, then the newest frames shown, the list placed for the offset it was drawn at | nothing of Lean's: it shows the newest frame handed over |
| Lean main | `App.step`, frame after frame | a free buffer from the compositor (at most two vsyncs); today also SQLite (the frame's reads) |
| reader (proposed) | the board's passes, on its own connection | SQLite |
| writer | the app's writes, one transaction a job | SQLite's write lock |
| node `runLoop` | the node: events, then the clock every `tickMs` | SQLite's write lock; `IO.sleep 5` when idle |
| socket readers, dials, acceptor | one dedicated thread each | `awaitUv`: its socket's promise |
| libuv loop | the sockets' I/O; resolves the promises | the OS |
| the task pool | picture decodes (`Pics.spawn`), row paints, dims, the camera's decode | nothing but CPU |

The wait-for graph has no edge from Lean main, the reader, the writer,
the node or a socket thread into the pool:

- Lean main reads a task only after `IO.hasFinished` says it is done
  (`Pics.finished`; `paintRow`'s paint and dim), and spawns without
  waiting. tests/Doors.lean checks that the counted picture code reaches
  no task but through its doors.
- The node's socket waits block their own dedicated threads on the libuv
  promise (`awaitUv`), never `Async.block`, which maps each result on the
  pool. tests/engine/PoolStarve fills the pool with busy tasks and times
  a 64 KiB frame over loopback: well under a second, where
  `Async.block` stalls until the pool drains.
- The one exception is development-only: Chaos's loader waits on a pool
  task from a dedicated thread.

### What follows

- **Frame time is bounded under any pool load.** Lean main's frame is its
  own work plus a buffer wait of at most two vsyncs. Once the frame reads
  only the board (`frame_reads`), that work is `frame_work`: O(rows on
  screen), independent of N, of SQLite's latency and of the decoders'.
  With the pool's P workers busy on P cores, a fair scheduler gives Lean
  main at least half a core, so a frame takes at most twice its work.
- **The user always sees something move.** The compositor places the
  list for the vsync's offset at every vsync, whatever Lean is doing, so
  the last frame slides with the finger. Rows a slide uncovers beyond
  the overscan show the background until the next frame, at most one
  bounded frame later; that frame covers the viewport with painted rows
  or placeholders (holmes-1e's coverage law). A slow read or a slow
  decode only makes a row's value or picture late
  (`settle_passes`, picture freshness below), never a frame.
- **Sync's round bounds become wall time.** The node's thread does a
  round's messages in sequence, each bounded in the meter (a3's
  `round_depth`, `cold_answer`, the frame cap); with `Costs.time` and the
  phone's `Units`, a round takes at most (2k + 3) × (RTT + one message's
  bounded work), and the clock's work per tick is bounded the same way.
  The runner handles one event per turn and checks the clock every
  turn, so the clock is never starved by events, and events are handled
  in order.
- **Picture freshness.** A picture's decode is spawned once
  (`Pics.image_twice`); with at most `inflight` decodes on the pool,
  nearest the viewport first, a picture waits at most
  ⌈inflight / P⌉ + 1 decodes of at most one `slice` each. Today the
  number in flight is not capped (❌, a3's row).

### Assumed

- **The OS** schedules runnable threads fairly (each of R runnable
  threads on a core gets at least 1/R of it), and the compositor's
  thread is scheduled at every vsync.
- **No collector pauses**: Lean frees by reference counting, so no
  thread stops for another's garbage; an allocation is bounded work.
- **The runtime's C**: libuv's loop runs on a thread of its own, not the
  pool; `IO.Ref`'s swap is a short spin, never a wait on another
  thread's work; SQLite's WAL lets a reader run beside a writer.
- **SQLite**: the B-tree assumption above, and that the plan of each
  statement is the one engine/core/CostStore.lean charges.
