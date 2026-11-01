# Good worlds: one top theorem

The user's target (2026-11-01): a good state, plus any possible event,
gives a good state, community-wide, over every concurrent event (ops,
wire and lifecycle), over the running code:

```
Good w → Legal P adv w a → Good (w.step P a)      so      Good w₀ → ∀ k, Good (E.world k)
```

Every other law hangs under it, as a conjunct of `Good` or a corollary of
`good_always`. This note fixes the shape; engine/world/Good.lean is the
interface every later lane plugs into, and engine/world/PlainGood.lean
is its first instance (`Plain.good_always`).

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
the `Keeps` proofs of the world-level ones.

## The event set

The World's acts: deliver, dup, drop, tick, write, restart, close,
connect (harness only) and inject (the attacker's). What the running app
does beyond them, and how each enters:

| Event | How it enters | Refinement to state and prove | Owner |
|---|---|---|---|
| Crash (kill -9, OOM, power) | `restart i`, as now | `P.crash` is what SQLite has committed: the store, and for production `Memory.retries`; the entropy cursor and every session are lost. Atomicity of an entry point's transaction stays an assumption, tested by the kill -9 suite. | 71 (production `crash`) |
| Suspend (background, service off; always on iOS) | **Derived**, not a new act. `App.suspend` stops the runner (`Runner.stop`) and journals parked writes; every socket is dead after a mobile sleep, so all are closed. At peers: `close j (addr i)`. In flight to i: `drop`. At i: no act until resume. | A safety law over all executions already covers any subsequence of acts, so "no ticks while suspended" needs no act. For liveness, a suspended node is offline: `Net.Live` drops its edges. | new lane: app lifecycle |
| Resume | **Derived**: `restart i` (`Runner.start` boots `Node.boot` of the store's log, floor 0, which is exactly `Setup.reboot`), then `write i journal`, then `tick i` (dial). | R1: `Runner.start` builds `Setup.reboot`'s node. R2: `replayStoppedNodeWrites` submits each parked write once, in order, through `onWrite` (honest per `P.honest`). | new lane: app lifecycle |
| Background, service on (Android) | No event: the runner keeps running. | None. | — |
| App write journal | A separate layer above the World, whose only World effect is `write i ops`. | The App's outbox and journal submit exactly the user's ops, each once (R2 above), so `P.honest i` is what the App writes. | new lane: app lifecycle |
| Renderer | A separate layer: reads only. | Its store effect is none (lane reads' generic `Reads`), and its writes are App writes. | lane reads |
| Clock | `tick i t`, with `Legal` keeping `now` monotone. | The runner's clock is `IO.monoMsNow`: assumed monotone. | — |
| TCP | `flight` and `close`. | S1 (no loss without a close, no duplicates), audited against Tcp.lean. | as now (docs/PROOFS.md) |

So lifecycle adds no act: suspend and resume refine to sequences of
existing ones. What it adds is two refinement laws (R1, R2) over App code,
and a production `crash`.

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
| community trust | node | at rest, admitted/removed/rooms facts are the spec's | `admitted_node`, `removed_node`, `rooms_cut_node`, `connect_iff_node` (over `Inv ∧ queue = []`) | restate over `store` + urgent settled | join lane, then 80 |
| secrets purged | node | a closed session's secrets and couriers are gone | `purge_gone`, retirement | as a `Local` | 71 |
| `Sent` | world | every packet in flight was sent in the past | `sent_keeps` (any setup) | — | done |
| provenance | world | a packet with `src = some i` is a frame node i's entry point sent (`FramesOk`/`FramesBy`); injected bytes are in `adv w` | `entry_fresh`, `removal_reaches_session` (per node) | lift per-node frames to `wire` | 71 |
| secrecy | world | no packet on `wire` lets a non-member open a session's frames or a room's content | Noise `kk_secret`, pair secrecy (lq-pairsec) | `adv` as the Dolev–Yao closure of `wire`; the conjunct over `wire` | 71, pair-secrecy lane |
| removal cuts off | world | after a removal is settled at i, no frame i sends carries the removed member's rooms | `removal_reaches_session`, `rooms_cut` | over `wire`, with `settled` | 80 / 71 |

Step guarantees (`Guar`): each store moves only by turns and purges
(`Plain.moves_always`, giving `grows`, `keeps_op`, `shared_retained`);
time never goes back (`step_now`); the wire only grows.

## The corollaries

With `Good` at every step of every execution, each headline README law
becomes a statement over every execution and every node:

| README law | Corollary | From |
|---|---|---|
| Verdicts are the spec's, and final | `Plain.verdicts_spec`, ∀ k i | `store`, `settled` |
| Honest nodes agree | `Plain.agree`, ∀ k k' i j | `store`, `settled` |
| Shared stores only grow; purge is safe | `Plain.grows`, `keeps_op` | step guarantee |
| Everyone converges | `Plain.converge`, `want_reaches` | `managed`, `owes`, `bounded`, `ix` (via the `_start` projections) |
| The Community laws hold in the running node; removal cuts off | `connect_iff`, `removal_cuts_off`, ∀ k i | `store`, urgent `settled`, community trust (join lane) |
| Sessions are secret | per-wire secrecy | `secrecy` (71) |

## The serial gate: `Pieces` beyond `Plain`

Today `Pieces` (engine/world/InvIx.lean) is fixed to a3's
`Engine.Sync.Setup` (fixed rooms, plain frames) on `HeldM`, and the
`onX_keeps` proofs unfold `HeldM.run`. The production node runs on
`Connection.Execution.M` (`Memory → α × Memory`) with `Connection.hooks`,
a catalog and a retry store. The next serial step generalizes `Pieces`
to any `Setup` whose `run` is lawful, so the same `onX_keeps` proofs
serve both, and the 49 duplicated `*_reads` lemmas (audit) go.

A sketch, for a8 and 71 to react to:

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
  serve : ∀ n cid now s, Φ n s → Φ' (P.run (n.serveOwed (P.sync i) cid now) s)
  finish, setAddr, heat, drop, opens   -- as today
  -- new: what production hooks do that the plain ones do not
  follow  : ∀ n now s, Φ n s → Φ' (P.run (n.follow (P.sync i) now) s)    -- established → managed
  react   : ∀ n s, Φ n s → Φ' (P.run (n.react (P.sync i)) s)             -- hooks' writes
  dial    : ∀ n now s, Φ n s → Φ' (P.run (n.dialStore (P.sync i) now) s) -- dialed ops stored
  sweep   : ∀ n cid s, Φ n s → Φ' (P.run (n.sweep (P.sync i) cid) s)     -- the catalog
  retire  : ∀ n s, Φ n s → Φ' (P.run (n.retire (P.sync i)) s)            -- purge retired
  -- hooks that only read (sealFor, openFrame, rooms, retryKey) and draw
  -- entropy (Fresh) need no field: a Reads law (lane reads) shows they
  -- leave Φ as it was, given Φ ignores the entropy cursor.

theorem Pieces.local (hP : P.Lawful) (h : ∀ i, Pieces P i (Φ i)) (boot : …) : Local P Φ Φ
```

(`Φ' (n, s)` abbreviates `Φ n.1.1 n.2` on a run's result; the names of
the new node pieces follow whatever `Node.onTick`/`finish` call when
they are split.) Order: lane reads' generic `Reads` first; then
`Setup.Lawful` with instances for `HeldM` (`rfl`) and `Execution.M`
(`rfl`); then `Pieces` and the `onX_keeps` over `P.run`, replacing
today's; then the production `Setup` (the n-node World on
`Connection.hooks`), whose `Good` adds the production conjuncts above.
This lane does not start it: it gets its own brief once this design is
accepted.

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
  `agree` over stores whose urgent facts are settled; the conjunct for
  the rest is a liveness law under fair ticks, not a conjunct of `Good`.

## What `Plain.good_always` covers, and what it does not

Covers: every node of the plain World (n nodes running the real
`Engine.Sync.Node` on held stores, fixed rooms, frames in the clear,
harness sessions), at every step of every execution from empty stores,
against any attacker: `managed`, `owes`, `bounded`, `ix`, `store`,
`settled` (as queue = []), and `Sent`; and each step's store moves.

Does not cover: the production hooks (sealed sessions, the handshake,
rooms from the store); lifecycle (R1, R2, production `crash`); the
world-level conjuncts beyond `Sent` (provenance, secrecy, removal over
the wire); and the community conjuncts.
