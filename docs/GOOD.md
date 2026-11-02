# Good worlds: one top theorem

The user's target (2026-11-01): a good state, plus any possible event,
gives a good state, community-wide, over every concurrent event (ops,
wire and lifecycle), over the running code:

```
Good w → Legal P adv w a → Good (w.step P a)      so      Good w₀ → ∀ k, Good (E.world k)
```

The safety laws hang under it, each as a conjunct of `Good` or a
corollary of `good_always`. The liveness laws (convergence, delivery
bounds) are a separate spine, under `Edge` and the fair-network premises;
`Good` supplies the invariants they consume. This note fixes the shape;
engine/world/Good.lean is the interface every later lane plugs into, and
engine/world/PlainGood.lean is its first instance (`Plain.good_always`).

## The interface (engine/world/Good.lean)

All of it is over any World setup `P : Setup F M S`: any node monad, any
hooks, any attacker `adv`.

- **`step_touch`**: a legal step touches each node at most once, by one
  entry point (`Runs`: onFrame, onTick, honest onWrite, onClose, the
  harness's connect) or by a restart (`Setup.reboot`, from `P.crash`).
  This is the only case analysis over `Act`; everything below is a
  corollary.
- **Node-local conjuncts** (`Local P G Φ`): every entry point the World
  runs at node i, and a restart, take a node and box satisfying `G` to
  ones satisfying `Φ`. They are about the node alone, so a `Local` proof
  holds whichever World runs the node and whatever bytes reach it.
  `Local.keeps` lifts `Local P G G` to the world (`Nodes P G`).
- **World-level conjuncts** (`Keeps P adv G C`): every legal step from a
  world satisfying `G` reaches one satisfying `C`. `Sent` (every packet in
  flight was sent no later than the clock) is the first, for any setup
  (`sent_keeps`).
- **Assume-guarantee**: each conjunct is proven under the whole, as
  `Local P Good Φᵢ` or `Keeps P adv Good Cᵢ`, and assembled with `mono`
  and `and`. `good_keeps` joins the two kinds: `Good P N W := Nodes P N ∧ W`.
- **Step guarantees** (`Guar`, and its node-local form `Boxes`): a
  relation between a world and the next, such as "each store moves only
  by write turns and purges". `Guar.always` gives it at every step.
- **Lifting**: `Keeps.reach` (every reachable world) and `Keeps.always`
  (every world of every execution).

An instance supplies, per node, the `Local` proofs of its conjuncts, and
the `Keeps` proofs of the world-level ones. A fact that follows from the
conjuncts at one state is a corollary, not a conjunct: it needs no
preservation proof of its own.

Wiring: the instance's laws (`Plain.good_always`, `Plain.good_keeps`,
`moves_always`, `verdicts_spec`, `Plain.agree`, the projections) and the
generic `Keeps.always`, `Guar.always`, `sent_keeps` class `world`. The
generic `step_touch`, `Local.keeps`, `Boxes.guar` and `good_keeps` name
the harness's `Node.connect` (through `Runs`), so they class `model` on
their own and stay out of tests/Axioms.lean; the World laws above use
them in their proofs.

## The event set

The World's acts: deliver, dup, drop, tick, write, restart, close,
connect (harness only) and inject (the attacker's). What the running app
does beyond them, and how each enters:

| Event | How it enters | Refinement to state and prove | Owner |
|---|---|---|---|
| Crash (kill -9, OOM, power) | `restart i` | `P.crash` is what SQLite has committed: the held store, session rows included (they are local ops), and `Memory.retries`; the entropy cursor is lost. Boot's crash recovery retires every session row it finds and purges its keys, so the production `Setup.reboot` must run that recovery, not only `Node.boot` (a World change: a `recover` step in `restart`). Atomicity of an entry point's transaction stays an assumption, tested by the kill -9 suite. | 71 (production `crash`, the recovery link), a8 (`restart`) |
| Suspend (background, service off; always on iOS) | **Derived**, not a new act. `App.suspend` stops the runner (`Runner.stop`) and journals parked writes; every socket is dead after a mobile sleep, so all are closed. At peers: `close j (addr i)`. In flight to i: `drop`. At i: no act until resume. | A safety law over all executions already covers any subsequence of acts, so "no ticks while suspended" needs no act. For liveness, a suspended node is offline: `Net.Live` drops its edges. | new lane: app lifecycle |
| Resume | **Derived**: `restart i` (`Runner.start` boots `Node.boot` of the store's log, floor 0, which is `Setup.reboot`), then `write i journal`, then `tick i` (dial). | R1: `Runner.start` builds `Setup.reboot`'s node. R2: `replayStoppedNodeWrites` submits each parked write once, in order, through `onWrite`, after the old runner has finished with SQLite (runtime evidence today: the AppSuspendJournal and AppRunnerFailure suites). | new lane: app lifecycle |
| Background, service on (Android) | No event: the runner keeps running. | None. | — |
| App write journal | A separate layer above the World, whose only World effect is `write i ops`. | The App's outbox and journal submit exactly the user's ops, each once (R2), so `P.honest i` is what the App writes. | new lane: app lifecycle |
| Renderer | A separate layer: reads only. | To prove: its store effect is none, and its writes are App writes. No law states it yet; lane reads' generic `Reads` is the tool. | to assign |
| Clock | `tick i t`, with `Legal` keeping `now` monotone. | The runner's clock is `IO.monoMsNow`: assumed monotone. | — |
| TCP | `flight` and `close`. | S1 (no loss without a close, no duplicates), audited against Tcp.lean: an [env] premise. | as now (docs/PROOFS.md) |

So lifecycle adds no act: suspend and resume refine to sequences of
existing ones. What it adds is two refinement laws (R1, R2) over App code,
and a production `crash` with recovery.

## The conjuncts

Node-local conjuncts are `Fin n → Node → S → Prop`, proven per entry
point (a `Local`). World-level conjuncts are about the network or the
wire (a `Keeps`).

| Conjunct | Kind | Statement | Feeds it today | Missing | Owner |
|---|---|---|---|---|---|
| `managed` | node | plain: no managed sessions; production: managed sessions are the established ones | `managed_local` | production form | 71 |
| `owes` | node | every session owes only ids in its queue | `oq_pieces` | `Pieces` over production hooks | a8 / 71 |
| `bounded` | node | every queue holds at most `maxKnown` ids | `bounded_pieces` | same | a8 / 71 |
| `ix` | node | the index covers the store, keyed; the store holds each op under its id, in its log | `ix_pieces`, `boot_ixinv` | production: catalog sweep and purges (purges take only room-less ops, so covering survives) | a8 / 71 |
| `store` | node | the store is one the engine reaches from its log (`Held.Reachable`), so the store invariant `Inv` holds (`reach_inv`) | `Moves.store_reachable` over `entry_fresh`; production `world_step_moves` | `Runs` for the production setup | 71 |
| `waiting` | node | **urgent work settled after every step** (`UrgentWaiting`): every undecided urgent op whose closure is all urgent waits on its undecided requirements, so its status is its Spec verdict over the stored ops (`urgent_spec`); the rest settle after finitely many idle turns (see "Drain-cap") | `Moves.store_waiting` (`turn_waiting`, `purge_waiting`); `waiting_empty` at the start | — | done (0f) |
| secrets purged | node | a closed session's secrets and couriers are gone, after a close and after crash recovery | `purge_gone`, retirement; "each completed close, including crash recovery, leaves no row" | a `Local`: it is about which sessions the node holds open, so it needs its own proof per entry point (a close retires and purges; an open writes secrets only for an open session) and at reboot (recovery) | 71 |
| `Sent` | world | every packet in flight was sent in the past | `sent_keeps` (any setup) | — | done |
| provenance | world | a packet with `src = some i` is a frame node i's entry point sent; injected bytes are in `adv w` | per node: `FramesOk`/`FramesBy` (`entry_fresh`, `removal_reaches_session`) | lift to `wire` with `Sent` and `step_touch` | 71 |
| secrecy | world | no packet on `wire` lets a non-member open a session's frames or a room's content | handshake keys: Noise `kk_secret`; pair secrecy (lq-pairsec) | frame secrecy needs AEAD as a symbolic constructor in the same Dolev–Yao closure (`sealFor_opens` is correctness, not secrecy); `adv` built on holmes-80's `Derivable O K` (NoiseSymbolic), shared with 71's signature model (sig-model) so one closure covers handshake, frames and signatures. The honest-key exclusion in `Legal` is a [crypto] premise (`Trust.NativeCrypto`, the coming Ed25519 soundness Prop). | 71, 80 |
| removal cuts off | world | after a removal is settled at i, no frame i sends carries the removed member's rooms | `removal_reaches_session`, `rooms_cut` | over `wire`, with `settled` | 80 / 71 |

Step guarantees (`Guar`): each store moves only by turns and purges
(`Plain.moves_always`, giving `grows`, `keeps_op`, `shared_retained`);
time never goes back (`step_now`); the wire only grows.

## The corollaries

With `Good` at every step of every execution, each headline safety law
becomes a statement over every execution and every node:

| README law | Corollary | From |
|---|---|---|
| Verdicts are the spec's, and final | `Plain.verdicts_sound`, ∀ k i: every stored verdict is the spec's; `Plain.verdicts_spec`, ∀ k i: for an op whose closure is all urgent, a verdict is stored iff the spec gives it | `store`; `store`, `waiting` |
| Honest nodes agree | `Plain.agree_decided`, ∀ k k' i j: the same ops received, in any orders, give the same verdict on every op both decided; `Plain.agree`: and on every op whose closure is all urgent, decided or not (`urgent_agree` at every node) | `store`; `store`, `waiting` |
| Shared stores only grow; purge is safe | `Plain.grows`, `keeps_op` | step guarantee |
| The Community laws hold in the running node: admitted, removed, rooms, `connect_iff`, `removal_cuts_off` | the `*_node` laws, ∀ k i | `store` + `waiting`, through `urgent_valid_iff` and `sum_project_node`; lane join's `trace_good` is the production version |
| Sessions are secret | per-wire secrecy | `secrecy` (71) |

**Not a corollary: liveness.** `Plain.converge`, `offline` and
`want_reaches` are the liveness spine, under `Edge` and the fair-network
premises (`Net.Admits`); `Good` gives only the invariants they consume
(`managed`, `owes`, `bounded`, `ix`, through the `_start` projections),
and `want_reaches` can take them in one go as `good_node E m a`.

## The serial gate: `Pieces` for any setup (built)

engine/world/Pieces.lean proves a node invariant over every entry point
once, for any World setup whose run is a run, under the node's own hooks,
whatever they are. The plain World is its first instance; the production
World on `Connection.hooks` is the next.

- **`Lawful run`**: `run` is a monad morphism into state passing
  (`run (pure a) s = (a, s)`, `run (x >>= f) s = run (f (run x s).1) (run x s).2`).
  Instances: `Plain.lawful` (HeldM) and `Connection.Execution.lawful`
  (`M`, the entropy tape included), both `rfl`.
- **`MetaOnly run held p`**: p leaves the held store as it is
  (`∀ s, held (run p s).2 = held s`); it may move only what a node
  invariant ignores. A node invariant is `Φ : Node → Held F → Prop`,
  read at `P.held s`, so it ignores the entropy cursor and
  `Memory.retries` by construction. Bridges: `Plain.reads_meta` and
  `Execution.reads_meta` (every `Reads` step is `MetaOnly`), and
  `Execution.save_meta` (the production `retryStore.save`).
- **`Pieces P i Φ`**: what Φ must survive at node i, each piece stated
  over its whole run result (`Ok`), so a relation between a piece's start
  and its result (`Steps`) can reuse the skeletons:

  | Field | The piece |
  |---|---|
  | `write`, `store` | a write turn; storing (put, fanout, the react loop) |
  | `recv`, `tick` | a payload or the clock on a session, on its connection with any rooms the hook gave (`c.carry rs`), then `apply` |
  | `serve` | serving a queue, under any setting with the node's family and hooks (the tick serves on `afterActs`) |
  | `sweep` | a catalog sweep, under the node's setting with any transport room |
  | `opens`, `follow`, `flush` | opening a session; following the established (open, drop); handing out the outbox |
  | `calls` | steps that leave the node as it is (`Call`): the hooks `rooms`, `openFrame`, `recv none`, `dial`, `retired`; sealing; `endSession`, the close-purge path. They may move the store; Φ must survive |
  | `setAddr`, `heat`, `drop`, `sent`, `clear`, `retries` | pure node updates |

- **The entry points, once** (`finish_keeps`, `onClose_keeps`,
  `connect_keeps`, `onWrite_keeps`, `onSealed_keeps`, `onFrame_keeps`,
  `onTickDirect_keeps`, `onTickReserved_keeps` with `sweepAll_keeps`,
  `onTick_keeps`), and **`Pieces.local`**: `Lawful` + every node's
  pieces + boot give `Local P Φ Φ` (engine/world/Good.lean).
- **The plain instance**: `Plain.pieces` builds a plain node's `Pieces`
  from the few its hooks reach (following, the outbox, the calls and the
  sweep are the plain hooks': nothing established, no outbox, calls that
  only read, no catalog). `managed_pieces`, `oq_pieces`, `ix_pieces` and
  `bounded_pieces` are its instances; `Plain.always`, `managed_nil` and
  `Plain.good_always` rest on `Pieces.local`.
- **Teeth** (`dial_mutant_unindexed`, a negative control): a dial hook
  that stores an op with a write turn of its own, never indexing it, has
  no `Pieces` for the index's cover.

**Next:**
1. The production `Pieces` instances for `Connection.hooks` on
   `Execution.M` (holmes-71), from the `Reads`/`MetaOnly` hook laws and
   the store's `Moves` for the purges (`endSession`, crash recovery).
2. `Steps P i R`, the relational sibling over the same fields and
   skeletons, so the drain comes from per-piece facts (holmes-a8).
3. The production n-node `Setup`, with crash recovery in `restart`
   (holmes-a8 and holmes-71).
4. Done with drain-cap: `onTick` starts with an idle turn, `Turn.turn fam
   []`, and every `Pieces` has an `idle` arm for it (plain instances keep
   their conjuncts because the turn changes only the store's tables).

## Drain-cap: what "settled" means

holmes-77 chose job closure (2026-11-01): a turn judges, transitively,
the urgent waiters its own decisions wake. The store conjunct is:
**urgent status = Spec after every step** (`urgent_spec`, no premise),
and the rest settle after finitely many idle turns.

- **The urgent class** (holmes-0f): own writes; connection ops
  (handshake, established, session); and `Family.urgent`, which for
  Community is root, invite, request, grant, remove, approve and admit.
- **queue = [] after every entry point stops holding.** A turn ingests,
  judges its job ahead, closes over the urgent waiters each decision
  wakes, then makes at most 1024 FIFO pops; other content may carry to
  later turns.
- **What 0f states:** `urgent_spec`, every stored urgent op's status is
  its Spec verdict over the stored ops, after every step, with no
  premise; `turn_cost`, amortized over the wait-edge potential, with a
  spike bound.
- **A family obligation, `urgent_closed`:** urgent kinds cite only urgent
  kinds. Each family declares it, so a turn's closure over urgent waiters
  never waits on a non-urgent op.
- **The community laws keep their meaning** through
  engine/core/Locality.lean (`spec_local`): a membership op's verdict
  depends only on the ops it cites, all of which are urgent
  (`urgent_closed`). So `connect_iff`, `removal_cuts_off` and the
  `*_node` laws take "urgent status = Spec" in place of `queue = []`, and
  conclude about the same facts. Reads stay over Valid ops only.
- **The plain instance** has `waiting : UrgentWaiting fam h.db` in place
  of `queue = []` (`waiting_local`, from `Moves.store_waiting`).
  `verdicts_sound` keeps every stored verdict the spec's;
  `verdicts_spec` is exact for ops whose closure is all urgent;
  `agree_decided` keeps agreement on every op both nodes decided, and
  `agree` covers every urgent op, decided or not. The rest settling is a
  liveness law under fair ticks (`spec_eventually`, `closure_delivered`
  under `Ticks`), not a conjunct of `Good`.

## What `Plain.good_always` covers, and what it does not

Covers: every node of the plain World (n nodes running the real
`Engine.Sync.Node` on held stores, fixed rooms, frames in the clear,
harness sessions), at every step of every execution from empty stores,
against any attacker: `managed`, `owes`, `bounded`, `ix`, `store`,
`waiting`, and `Sent`; and each step's store moves.
Witnessed on a concrete run (tests/vacuity/Good.lean): two nodes write
the same two ops in opposite orders; `agree_decided` and
`verdicts_sound` are applied natively, with the ops' SHA-256 ids decided
by running them, and `agree` and `verdicts_spec` on the same run over a
family whose every op is urgent.

Does not cover: the production hooks (sealed sessions, the handshake,
rooms from the store); lifecycle (R1, R2, production `crash` and
recovery); the world-level conjuncts beyond `Sent` (provenance, secrecy,
removal over the wire); drain-cap's urgent class; and liveness.
