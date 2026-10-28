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

Proposed, with its law statements; not yet proven or built.

The frame never reads the store. A reader on its own thread (dedicated,
its own connection, one read transaction per pass) owns the journal's
cursor, the live cache of list answers, the outbox, and every view's
evaluation. It publishes each value the frame wants to a `Board`,
versioned: a refill whose value is equal keeps its version, and a
different one takes the next version of one counter and is marked moved.
The frame takes the moved set with one atomic swap and works only on the
values in it that are on screen.

The signal is the effect (a value moved) at the moment it lands, not its
cause (a commit's notice): with refills off the frame, the two land in
different frames, and a frame gated on notices misses the refill that
lands after its notice was taken (holmes-1e's TwoNodes failures).

| law | statement |
|---|---|
| `put_same` | a refill equal to the held value changes nothing |
| `put_moves` | a different or new value takes the next version and is moved |
| `ver_ident` | along any run, one version of a want is one value |
| `take_complete` | between two takes, every want whose version moved is in the moved set |
| `inv_step`, `settle` | with no commits after seq s, after ⌈dirty / refill⌉ passes and one frame, the screen's values equal the store's |
| `notice_gated_stale` | the mutant: a frame gated on notices stays stale forever on a three-step trace |
| `frame_reads` | the frame's step makes no store read and no list, and reaches no SQL, decrypt or decode but through `Pics.spawn` (Doors) |
| `frame_work` | the frame's work is at most a + b · rows on screen + the moved values' sizes |
| `frame_idle` | nothing moved, no event, no scroll, no paint finished: no work, and the same rows out |
