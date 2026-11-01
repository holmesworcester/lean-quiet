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
| `settled` | node | **urgent facts are settled after every event**; the rest settle after finitely many idle turns (see "Drain-cap") | `store_settled` (queue = []), until drain-cap lands; then `turn_urgent`, `urgent_settled` | the fit premise discharged from item 5's intake cap | 0f |
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
| Verdicts are the spec's, and final | `Plain.verdicts_spec`, ∀ k i | `store`, `settled` |
| Honest nodes agree | `Plain.agree`, ∀ k k' i j: the same ops received, in any orders, give the same verdicts (`order_free` at every node) | `store`, `settled` |
| Shared stores only grow; purge is safe | `Plain.grows`, `keeps_op` | step guarantee |
| The Community laws hold in the running node: admitted, removed, rooms, `connect_iff`, `removal_cuts_off` | the `*_node` laws, ∀ k i | `store` + urgent `settled`, through `status_iff_spec` and `sum_project_node`; lane join's `trace_good` is the production version |
| Sessions are secret | per-wire secrecy | `secrecy` (71) |

**Not a corollary: liveness.** `Plain.converge`, `offline` and
`want_reaches` are the liveness spine, under `Edge` and the fair-network
premises (`Net.Admits`); `Good` gives only the invariants they consume
(`managed`, `owes`, `bounded`, `ix`, through the `_start` projections),
and `want_reaches` can take them in one go as `good_node E m a`.

## The serial gate: `Pieces` beyond `Plain`

Today `Pieces` (engine/world/InvIx.lean) is fixed to a3's
`Engine.Sync.Setup` (fixed rooms, plain frames) on `HeldM`, and the
`onX_keeps` proofs unfold `HeldM.run`. The production node runs on
`Connection.Execution.M` (`Memory → α × Memory`) with `Connection.hooks`,
a catalog and a retry store. The next serial step generalizes `Pieces`
to any `Setup` whose `run` is lawful, so the same `onX_keeps` proofs
serve both, and the 49 duplicated `*_reads` lemmas (audit) go.

The sketch, with a8's and 71's review folded in:

```lean
/-- `run` is a monad morphism into state passing. -/
structure Setup.Lawful (P : Setup F M S) : Prop where
  pure : ∀ (a : α) s, P.run (pure a) s = (a, s)
  bind : ∀ (x : M α) (f : α → M β) s, P.run (x >>= f) s = P.run (f (P.run x s).1) (P.run x s).2

/-- What a node invariant must survive, piece by piece, at node i of P. -/
structure Pieces (P : Setup F M S) (i : Fin P.n) (Φ : Node → S → Prop) : Prop where
  -- as today, with P.run for HeldM.run and (P.sync i) for S.sync s:
  write : ∀ n ops s, Φ n s → Φ' (P.run (n.write (P.sync i) ops) s)
  store : ∀ n ops mine s, Φ n s → Φ' (P.run (n.store (P.sync i) ops mine) s)
  recv  : ∀ n cid c b now s, n.conn? cid = some c → Φ n s →
            Φ' (P.run (do let rs ← (P.sync i).hooks.rooms cid
                          let st ← Conn.recv … (c.setRooms rs) b now
                          n.apply (P.sync i) cid st now) s)
  tick  : …  -- the same with Conn.tickGive
  -- the tick serves on `n.afterActs (P.sync i) out`, a different Sync
  -- (room, retryRoom changed): keep today's form, any y with P's fam and hooks
  serve : ∀ (y : Sync F M), y.fam = (P.sync i).fam → y.hooks = (P.sync i).hooks →
            ∀ n cid now s, Φ n s → Φ' (P.run (n.serveOwed y cid now) s)
  finish, setAddr, heat, drop, opens   -- as today
  -- new: what production hooks do that the plain ones do not; names follow
  -- the real split of Node.onTick / finish / onClose
  follow  : ∀ n now s, Φ n s → Φ' (P.run (n.follow (P.sync i) now) s)    -- established → managed
  react   : ∀ n s, Φ n s → Φ' (P.run (n.react (P.sync i)) s)             -- hooks' writes
  dial    : ∀ n now s, Φ n s → Φ' (P.run (n.dialStore (P.sync i) now) s) -- dialed ops stored
  sweep   : ∀ n cid s, Φ n s → Φ' (P.run (n.sweep (P.sync i) cid) s)     -- the catalog
  retire  : ∀ n s, Φ n s → Φ' (P.run (n.retire (P.sync i)) s)            -- purge retired
  closing : ∀ n addr s, Φ n s → Φ' (P.run (n.closePurge (P.sync i) addr) s) -- onClose's purge path

/-- Effects that need no field, each by its own small law:
- Reads (lane reads): rooms, sealFor (which may return none after a
  size check), openFrame, retryKey, and Fresh's entropy draws.
- MetaOnly (new, 71): the held store and index are unchanged, only
  per-peer metadata moves: the catalog sweep's durable cursor
  (`retryStore.save`, kept in `Memory.retries`).
Φ must ignore the entropy cursor and `retries`. -/

theorem Pieces.local (hP : P.Lawful) (h : ∀ i, Pieces P i (Φ i)) (boot : …) : Local P Φ Φ

/-- The relational sibling (a8): progress facts are two-state relations,
not invariants ("x waits no further back, or its op went out", the drain).
R is reflexive and transitive; the fields are Pieces' with "R before after". -/
structure Steps (P : Setup F M S) (i : Fin P.n) (R : Node × S → Node × S → Prop) : Prop where
  refl : ∀ x, R x x
  trans : ∀ x y z, R x y → R y z → R x z
  write, store, recv, tick, serve, finish, setAddr, heat, drop, opens, …

theorem Steps.local (hP : P.Lawful) (h : ∀ i, Steps P i (R i)) : Boxes P … R
```

(`Φ' (n, s)` abbreviates `Φ n.1.1 n.2` on a run's result.) With
`Steps`, the drain (`step_waits`, `onTick_moves`, `onSealed_waits`)
comes from per-piece facts in the production World too; a8 owns it when
the gate opens.

Order: lane reads' generic `Reads` and a `MetaOnly` sibling first; then
`Setup.Lawful` with instances for `HeldM` and `Execution.M` (both `rfl`:
pure state passing, the entropy tape included); then `Pieces` and `Steps`
with the `onX` skeletons over `P.run`, replacing today's; then the
production `Setup` (the n-node World on `Connection.hooks`, with crash
recovery in `restart`), whose `Good` adds the production conjuncts
above. 71 sequences it after its landings and sig-model phase 2. This
lane does not start it: it gets its own brief.

## Drain-cap: what "settled" means

holmes-77 chose option (a) (2026-11-01). The store conjunct is: **urgent
facts are settled after every event, and the rest settle after finitely
many idle turns.**

- **The urgent class** (holmes-0f, a3/drain-cap 549688c): own writes;
  connection ops (handshake, established, session); and `Family.urgent`,
  which for Community is root, invite, request, grant, remove, approve and
  admit.
- **queue = [] after every entry point stops holding.** A turn makes
  urgent attempts, then at most 1024 FIFO pops, then urgent attempts
  again; other content may carry to later turns.
- **`turn_urgent`**: a closed urgent batch is decided within its own turn
  if the ready urgent work fits `urgentCap/2` per half. A removal cites
  only membership ops, so it wakes (`urgent_deferred`, `wake`) in the
  turn its last requirement is decided. The fit premise is to be
  discharged from item 5's intake cap, so that `urgent_settled` holds
  without premises.
- **The community laws keep their meaning** through
  engine/core/Locality.lean (`spec_local`): a membership op's verdict
  depends only on the ops it cites, all of which are urgent. So
  `connect_iff`, `removal_cuts_off` and the `*_node` laws take "urgent
  settled" in place of `queue = []`, and conclude about the same facts.
- **The plain instance today** uses `queue = []` (`NodeGood.settled`),
  which holds on main and on fd/world-port. When drain-cap lands,
  `settled` becomes `urgent : UrgentSettled fam h` (a `Local` from
  `turn_urgent`), `verdicts_spec` is restated over urgent ids, and
  `agree` over stores whose urgent facts are settled; the rest settling
  is a liveness law under fair ticks, not a conjunct of `Good`.

## What `Plain.good_always` covers, and what it does not

Covers: every node of the plain World (n nodes running the real
`Engine.Sync.Node` on held stores, fixed rooms, frames in the clear,
harness sessions), at every step of every execution from empty stores,
against any attacker: `managed`, `owes`, `bounded`, `ix`, `store`,
`settled` (as queue = []), and `Sent`; and each step's store moves.
Witnessed on a concrete run (tests/vacuity/Good.lean): two nodes write
the same two ops in opposite orders; `agree` and `verdicts_spec` are
applied natively, with the ops' SHA-256 ids decided by running them.

Does not cover: the production hooks (sealed sessions, the handshake,
rooms from the store); lifecycle (R1, R2, production `crash` and
recovery); the world-level conjuncts beyond `Sent` (provenance, secrecy,
removal over the wire); drain-cap's urgent class; and liveness.
