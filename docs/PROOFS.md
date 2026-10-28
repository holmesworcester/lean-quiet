# Proofs about many nodes

How Lean Quiet proves what n nodes do together: that they converge on
the whole community, within a bound, over the code that runs. Designed
by holmes-fd, 2026-10-28, for review. The user asked to "prove that
users always eventually sync the whole community", "in an n peer setup
assuming they all know about each other, and then if they all
transitively know about each other", and to "rely on proofs for this
stuff, not testing".

## Decisions

- **One world, n nodes, over the running code.** `World` holds n real
  `Node`s, each on a box of state a pure run of its monad threads, and
  the network as data (engine/world/World.lean). There is one step
  function. a3's two-node world and the pair-secrecy world are two
  instances of it, not two more worlds.
- **Every way in is a step, and only those.** The steps are: deliver,
  duplicate, drop, tick, a user's write through `Node.onWrite`, a crash
  and restart, the harness's `connect`, and the attacker's injection.
  Nothing else changes a node, so app writes that bypass the node are
  outside the world. The index law (`index_store_stmt`) then says what
  such writes break.
- **Generic in the monad.** `Setup.run : M α → S → α × S` runs node code
  on a box `S`. `HeldM` (a store) is the plain instance; the Connection
  family's adds entropy (`Fresh`); performance laws add a cost counter.
  A law proven for one instance transfers to another by an erasure
  lemma.
- **Fairness is a hypothesis, named in each theorem.** It covers four
  things: a knows-graph G, delivery within Δ on G's links, ticks every
  τ, and health (sessions up, rooms agreeing). Nothing about schedulers
  is built into the world. Whatever can later be proven is stated as a
  separate statement (session stability, handshake liveness), so the
  hypotheses only shrink.
- **Liveness is bounded progress, never bare "eventually".** Every
  liveness law has the form "within T ms", with T an explicit function
  of the hypotheses: `epoch = gap + roundTime` per edge, and
  `d · epoch` across a graph of diameter d. So liveness proofs are also
  latency bounds. Throughput and message counts are perf-proofs' (cost
  semantics), over the same world.
- **Liveness rests on rounds; the stream is latency.** As SYNC.md says,
  the per-edge bound cites only rounds and their have/want legs. The
  stream is proven separately (`stream_stmt`), as a latency law no
  liveness law needs. This is poc-13's "prove the anchor, gate the rest":
  an optimization that fails can cost time, never convergence.
- **Obligation chains, not invariants over every message.** A round's
  progress is a chain of packets in flight, each of whose delivery
  (within Δ, by fairness) puts the next one in flight, or completes.
  Each link of the chain is one entry point run on any state that
  satisfies a few world invariants. So a proof needs one lemma per kind
  of hop, not a characterization of everything in flight.
- **Node code must be provable.** No `while` or `partial` in anything a
  node runs: Lean makes them opaque, so no proof can say anything after
  them (finding 3). Loops are over lists or ranges.

## The world

```
World S n = { node : Fin n → Node, box : Fin n → S,
              flight : List Packet   -- in flight, any order
              wire   : List Packet   -- everything sent (the attacker's view)
              now, serial, wrote, delivered }
Packet    = { serial, src : Option (Fin n), origin, dst, bytes, sent }
Setup     = { n, sync : Fin n → Sync F M, addr, run, held,
              floor, crash, harness, honest, peek }
```

- **A step runs one entry point** (`World.enter`). The node and box
  move on, and the node's `Effects.send` become packets in flight and on
  the wire, each with a fresh serial, its sender, the sender's address
  and the time.
- **Delivery** removes one packet from `flight` (by index) and runs
  `Node.onFrame` at the node whose address is its `dst`, with `origin`
  as the source address. A packet to no node is lost.
- **Duplication** copies a packet in flight with a new serial and no
  sender, so fairness never obliges its delivery. **Drop** removes one.
- **Restart** keeps the box's store (`Setup.crash`) and boots the node
  from it (`Node.boot` over the store's log): sessions, rounds and
  everything else in memory are gone.
- **Injection** runs `Node.onFrame` on any bytes the attacker can make,
  with any origin. What it can make is the parameter
  `adv : World → ByteArray → Prop`:
  - `noAdv` (nothing);
  - anything, for robustness laws;
  - the pair-secrecy world's `Deliverable` (Dolev-Yao over `wire`).
- **`Legal`** gates acts. Time never goes back, a named packet is in
  flight, a user writes only what `Setup.honest` allows, `connect` only
  in the harness, and injections only what `adv` allows.
- **Executions** are infinite legal sequences (`Exec`); `Reachable` is
  the finite prefix closure, for safety.

**The plain setup** (`plain fam cfg n addr rooms`) is a3's world for n
nodes:
- fixed rooms per (node, session);
- frames in the clear (`plainSeal`);
- no handshake, so sessions come from `connect`;
- `HeldM`.

It models "everyone already knows and trusts each other". It is where
liveness is proven first.

**The Connection setup** (next) is the pair-secrecy world for n nodes:
- the Connection family's real hooks, so the trust rule gives rooms;
- handshakes make sessions;
- sealed frames;
- a box with entropy (`NodeM`).

### Porting the two existing worlds

- **a3/world** (`World`, `World.Step`, `stream_delivers`,
  `stream_offered`, `conn_answers_ids`) is `plain` with n = 2 and
  `Who ≅ Fin 2`. `World.Step S w w'` is `∃ a, Legal … noAdv w a ∧
  w' = w.step _ a`, delivering by index instead of a `pre ++ f :: post`
  split. a3's per-entry-point lemmas (`write_offers`, `hold_wants`,
  `want_sends`, `op_taken`, `seal_mem`, …) are about `Node` on `HeldM`.
  They port unchanged, and engine/world/Run.lean already carries the
  loop and `Keeps` machinery.
- **fd/pair-secrecy** (`Pair.World`, `Act`, `Setup.Step`/`Run`) is the
  Connection setup with n = 2:
  - Its `deliver` (any `Deliverable` bytes from any source) is the
    unified world's `inject` with `adv := Deliverable`.
  - Honest delivery (`deliver k`) hands over bytes already on `wire`.
    Those are always Deliverable, so every law proven against the
    attacker-only world holds with both kinds of delivery.
  - `PairOnly` (the users trust only each other) stays a per-step
    environment hypothesis of those laws.
  - `opened` is a ghost field that port adds.
  - `secrecy_stmt`, `authentic_stmt`, `frameReplay_stmt`,
    `bareReplay_stmt`, `deadDropped_stmt`, `heard_stmt`,
    `forward_stmt` and `live_stmt` keep their statements, with the world
    renamed.

## Executions and fairness

engine/world/Fair.lean. Each hypothesis is a definition over an
execution `E`:

| hypothesis | meaning |
|---|---|
| `Path G d i j`, `Diam G d`, `AllKnow G` | the knows-graph: who trusts whom; diameter d; complete |
| `Timely E G Δ` | every packet an honest node sends across an edge of G is delivered within Δ ms of its sending (so never dropped) |
| `Ticks E τ` | every node ticks at least every τ ms |
| `Unbounded E` | time passes |
| `Joined E i j cid k₀` | from step k₀ on: session cid is open at both ends, i dials, and each end's frames go to the other |
| `Healthy E G r k₀ N` | every edge of G is joined; its two ends' rooms agree and include r; every window of r holds at most N items |
| `Fair …` (Statements.lean) | all of the above, the setup's standing assumptions (`PlainOk`), symmetry of G, and 2Δ < patience |

What is assumed and what is derived:

- **Rounds are derived, not assumed.** "Every edge gets a round at
  least every k steps" follows from the code: the dialer opens a round
  `every` ms after the last one ended, at its next tick. So `gap`
  is a lemma (the cadence lemma), and only "sessions are up" is assumed.
- **Sessions up is assumed now, derived next:**
  - in the plain setup, from `session_stable_stmt`, once the patience
    fix lands (finding 1);
  - in the Connection setup, from handshake liveness: two nodes that
    trust each other and are both ticking end up with a session.
- **Rooms agreeing is assumed.** It is how "they all know about each
  other" enters. Under finding 2 it must cover all rooms, not just r.
  Its dynamic version, where rooms come from admissions that are
  themselves synced, is an induction over the admission order (next
  steps, item 8).
- **The bound N is a parameter.** `depth cfg N` is 1 in the leaf regime
  (N ≤ `leaf`: the opening lists ids). Otherwise it is `exchange_ends`'s
  2N + 1, which perf-proofs tightens to 2⌈log_fan N⌉ + 2.

## Liveness as bounded progress

Three layers, each with its own proof technique.

1. **The epidemic, proven** (engine/world/Epidemic.lean). If every edge
   of G carries any op held at one end to the other within B
   (`Edge E G r k₀ B`), then an op held anywhere is held d edges away
   within d · B (`hops`).
   - With growth (`grows_stmt`), it stays held.
   - So `converge_of_edge : edge_stmt → grows_stmt → converge_stmt` is
     proven.
   - Everyone knowing everyone is d = 1 (`converge_all_of`); two peers
     are a case of it (`converge_two_of`); three peers on a line are
     d = 2 (`converge_three_of`).
   - The argument is per op, so it needs no quiescence. New writes, and
     ops an attacker injects, never delay an op already held.
2. **The edge: cadence and a round.** An op x is held at i at time t.
   - The dialer's next round opens by t + `gap`, where
     `gap = every + (D+1)Δ + τ`: the cadence, the current round's end,
     and a tick.
   - Both snapshots of that round are taken after t, so they include x
     (`index_store`).
   - The round carries x across by `roundTime = (D+3)Δ`: D claim hops,
     then an offer, a want and the op.
   - So `epoch = gap + roundTime`.
   - The per-round lemma (`round_progress_stmt`) is proven as
     **obligation chains**:
     - an obligation is a packet in flight whose delivery runs an entry
       point that puts the next obligation in flight, or stores x;
     - `Timely` delivers each within Δ of its sending;
     - so x is stored within (hops) · Δ.
     - Each kind of hop is one lemma about one entry point, run on any
       state satisfying the world invariants (below).
     - Hops in the leaf regime, from i to j: claim of ids listing x →
       want naming x → x's bytes → stored. From j to i: claim → offer
       naming y → want → y's bytes → stored, with the `asked` invariant
       for an offer whose want was sent before.
     - Claim trees (fingerprints) add hops measured by
       `exchange_ends`'s count. Each piece of a mismatched range holds x
       or y's key, and the count of items falls.
3. **The potential, for the quiescent form.** Let
   Φ = Σᵢ |U ∖ Sᵢ|, where Sᵢ is node i's ops of room r and U is their
   union. With no writes or injections after k₀, U is fixed (no op from
   nowhere), so Φ never rises (growth). The per-op bound over the
   finite U zeroes Φ within d · epoch (`quiescent_stmt`). This is the
   "the whole community" form.

## Safety lifted to the world

Each safety law is one lemma per entry point (about `Node` on `HeldM`),
then induction over `Reachable`.

- `grows_stmt`: stores only gain shared ops.
  - In the plain setup nothing purges.
  - In the Connection setup purge takes only conn and local ops
    (`mem_purgeSet`).
- `index_store_stmt`: the in-memory room index names exactly the stored
  ops of each room.
  - `Node.write` adds exactly what a turn stored, and `Node.boot`
    rebuilds from the log.
  - This is "store = offered" for rounds: every op a node holds is in
    every round it opens or answers.
  - An app write that bypasses the node stores an op the index never
    gets, which no round offers until the next boot. That is exactly the
    bypass bug. The world has no such step. So the law's premise about
    the code is that platforms reach the store only through
    `Runner.write`, a code property tested by a CI check (next steps,
    item 9).
- `stream_stmt`: an op stored by a step is offered at once on every
  session that shows it, unless known there. This is a3's
  `stream_offered`, generalized to every step.
- `members_only_stmt`: every session frame an honest node sends carries
  sync messages and ops of the session's rooms only. This is ConnLaws's
  `recv_send`/`filed_send`/`tick_send`, through `Node` and `seal`.
- `waiting_closure_stmt`, `closure_agree_stmt`: below.

## Waiting ops

- **A write turn ends at rest.** On `Held`, a turn ingests and drains
  with the proven budget (`drain_bounded`), so after every step every
  node's queue is empty. Its verdicts are then the spec's over the ops it
  holds (`status_iff_spec`), given `CollisionFree` on its log.
- **So an op waiting on a missing requirement is judged in the step
  that brings the last one,** as if it had arrived after them
  (`waiting_closure_stmt`). Nothing has to "retry".
- **Holding the closure is enough.** If i judged x as v and j holds x's
  requirement closure at i, then j judged x as v (`closure_agree_stmt`,
  from `spec_local`).
- **With convergence, the union closes.** Every node ends up holding U,
  so every op's closure, and every node judges every op of U alike.
  Ops that wait forever at one node wait everywhere: their closure is
  missing from U, or contains a cycle.

## What stays assumed

- **Crypto.**
  - SHA-256 is collision-free on the ops received (`CollisionFree`,
    giving `Distinct`), and on the fingerprints' labels (`Sound`, for
    the claim-tree regime).
  - Ed25519 is unforgeable, for the membership laws the trust rule
    reads.
  - In the Connection setup, the symbolic Noise and AEAD
    (pair-secrecy's `Ideal`, `Apart`).
- **The network is a hypothesis, not a model of TCP.** The world's
  packets are what the runner's sockets carry: `Frame.lean`'s proven
  unframing, and `onFrame` with the socket's address. That the runner
  does this is tested by tcppair and jointcp, not proven. Timely
  delivery is assumed (`Timely`). Nothing assumes TCP's ordering.
- **Clocks.** Each node's `now` never goes back (`Legal`). Nothing
  relates two nodes' clocks: Δ and τ are in the world's time, and a
  node's patience and cadence are read from its own.
- **The seam calls only the entry points.** Platforms write through
  `Runner.write` (`onWrite`) and nothing else. This is a code property,
  tested, with a CI check to come.
- **SQLite behaves like `Held`.** The differential and crash tests check
  this, as for every engine law.
- **Lean's kernel, compiler and runtime.**

## Statements

engine/world/Statements.lean. Every `…_stmt` is a closed `Prop`.

| statement | says | status |
|---|---|---|
| `converge_stmt` | over a connected G of diameter d: an op any node holds, every node holds from some step on, within d · epoch | reduced to `edge_stmt` + `grows_stmt` (`converge_of_edge`, proven) |
| `converge_all_stmt` | everyone knows everyone: within one epoch | follows from `converge_stmt` (`converge_all_of`, proven) |
| `converge_two_stmt`, `converge_three_stmt` | 2 peers; 3 peers on a line (2 epochs) | follow from `converge_stmt` (proven) |
| `edge_stmt` | per-edge bound `epoch` under `Fair` | open: cadence + `round_progress` |
| `round_progress_stmt` | a round carries each side's ops to the other within `roundTime` | pilot: the leaf regime, i → j |
| `claim_delivers_stmt` | the pilot: claim of ids listing x, from i to j → j holds x within 3Δ | see "The pilot" |
| `session_stable_stmt` | a joined session is never dropped under Δ-timely delivery, 2Δ < patience | **false on today's code** (finding 1) |
| `grows_stmt` | shared stores only grow | open (the pilot proves the pieces it needs) |
| `index_store_stmt` | room index = stored ops of the room | open |
| `stream_stmt` | a stored op is offered at once on every session that shows it | open (a3's `stream_offered` covers writes) |
| `store_offered_stmt` | both of the above | open |
| `members_only_stmt` | session frames carry only the session's rooms' ops | open (ConnLaws per entry point) |
| `waiting_closure_stmt` | every node at rest; verdicts = spec | open (engine laws + Held's turn) |
| `closure_agree_stmt` | holding a closure, judge alike | open (`spec_local`) |
| `quiescent_stmt` | Φ never rises after quiescence, and is zero within d · epoch | open |

## The pilot

See engine/world/Pilot.lean and the report at the end of this section.

**Status: in progress.**

## Findings

Each finding is a statement above that is false of today's code, with
the witness proven in engine/world/Findings.lean.

1. **Patience counts from the last receipt, not from the wait's start**
   (`patience_drops_idle`).
   - A dialer's idle session opens a round at its cadence tick t. If
     the peer was last heard patience or more before t, the next tick
     drops the session, before any answer could arrive.
   - With the defaults (rounds every 30 s, patience 20 s), every
     session idle between rounds is dropped at its next round.
   - `session_stable_stmt` is false for every Δ > 0.
   - Fix: one field, `heard := now` in `Conn.start`.
2. **One room shown at only one end stops every round on the session**
   (`unshown_unanswered`, `no_round_while_open`).
   - The answerer sends nothing for a room it does not show.
   - The dialer then waits on that round forever, and patience drops the
     session.
   - It opens no round in any room meanwhile.
   - Rooms differ whenever one end has stored an admission the other
     lacks, which is the bootstrap.
   - Fix (for the user): answer with an empty claim list, which ends the
     round; or name shown rooms in the hello.
3. **`while` is opaque to proofs.** `Conn.walk` used `while`, which
   compiles through a `partial` definition, so after any tick or
   answered want a node's state was unknown to every proof. Fixed on
   this branch: a loop over `[0:cfg.walk]`, the same steps. `walk_keeps`,
   `walk_same` and `walk_idle` are about it, and syncpair passes.
4. **Snapshots are per room, not per round** (observed, not proven).
   - `onRbsr` drops every snapshot of room r on any message of r, so a
     duplicated empty message of an old round ends the current round
     at the dialer early.
   - The round continues from the live index, which only grows. That is
     harmless for liveness (the obligation argument never reads
     snapshots), but `exchange_complete`'s fixed-snapshot premise does
     not hold under duplication.
   - The planned rounds-as-ops, answered from the live store, need the
     growing-sets version anyway.

How the earlier bugs map onto the statements:

| bug | what catches it |
|---|---|
| app writes bypassing the node, never offered | `index_store_stmt`: the only write step is `onWrite`; bypass breaks index = store |
| a replayed purged request killing a live session | `session_stable_stmt` in the Connection setup, with `adv := Deliverable` (pair-secrecy's `bareReplay_stmt` is its instance) |
| `Conn.tick` measuring patience from the last receipt | `session_stable_stmt` (finding 1, witness proven) |
| a one-sided room's rounds never answered | `round_progress_stmt` needs the round to end; finding 2's witness |

## How a law about running code is proven

engine/world/Run.lean:

- **Running code on a held store is rewriting.** `HeldM.run_bind`,
  `run_pure`, `run_getOp` and `run_turn` reduce a do block's run to a
  term. Loops go through `Std.Legacy.Range.forIn_eq_forIn_range'` and
  `List.forIn_cons`.
- **Most code only reads** (`Keeps`). The `keeps [lemmas]` tactic proves
  it from a do block's structure: `walk_keeps`, `onWant_keeps`,
  `tick_keeps`.
- **Loop invariants:** `forIn_inv`. For example, `walk_same`: the walk
  touches only its frontier, offers and closures.
- **Hop lemmas** say: delivering a packet of this shape, to a node in
  any state satisfying the world invariants, puts a packet of the next
  shape in flight.
- **World invariants** are proven once for each entry point and lifted
  by induction over `Reachable`.

Rules for node code, so it stays provable:
- no `while`, `repeat` or `partial` in what a node runs;
- hooks only read, or write through `Turn`;
- every change to a node goes through an entry point.

## Next, in order

Rough sizes are lines of Lean.

1. **Finish the pilot's open pieces** (below), about 600: growth and
   index ⊆ store over every entry point (`onFrame`'s payload loop,
   `apply`, `store`/`fanout`/`settle`, `finish`/`seal`, `onTick`'s
   loop, `onWrite`, `connect`, restart).
2. **The reverse leg** (j's ops to i: offer, want, op), with the
   `asked` invariant, about 300. Then `round_progress_stmt` in the leaf
   regime.
3. **The patience fix and `session_stable_stmt`**, about 500: every
   wait is resolved within 2Δ of its start under `Timely`, given rooms
   agree.
4. **The cadence lemma (`gap`)**, about 200. Then `edge_stmt`, and so
   `converge_stmt`, in the leaf regime.
5. **Claim trees**, about 800: fingerprint hops as obligations measured
   by `exchange_ends`. The full `edge_stmt`.
6. **The remaining safety statements**, about 600: `stream_stmt`
   (generalizing a3's), `members_only_stmt`, `waiting_closure_stmt`,
   `closure_agree_stmt`, `quiescent_stmt`.
7. **The Connection setup**, about 400 to port pair-secrecy's laws
   onto this world, then handshake liveness (about 1000): two trusting,
   ticking nodes end up with a session, and a replayed request kills
   none.
8. **Dynamic trust**, size unknown: rooms from the trust rule, with
   admissions synced like any op, by induction over the admission
   order.
9. **A CI check** that only engine/core and engine/wire call `Turn`,
   `receive` or `Store.putOp`, about 30 lines of script.
