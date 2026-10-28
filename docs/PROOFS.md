# Proofs about many nodes

How Lean Quiet proves what n nodes do together over the code that runs:
that every op reaches every node within a bound, under a network that
loses, duplicates, reorders and delays, with nodes going offline,
crashing and restarting. Designed by holmes-fd, 2026-10-28, for review.

The user asked:
- "prove that users always eventually sync the whole community", "in an
  n peer setup assuming they all know about each other", "and then if
  they all transitively know about each other";
- "rely on proofs for this stuff not testing!";
- "make a Lean placeholder for the network with all of the parameters
  and behaviors we intend to tolerate, then attach full clients to it in
  the proof, then prove over many of them", covering chains and webs,
  and "reasonable or optimal propagation down a chain or in a star";
- "very strong but provable statements that take into account peers
  going offline and online, multiple peers interacting in all the ways,
  and sync of all the kinds of ops, both newly generated and existing";
- "data arriving concurrent to rounds from other peers, multiple rounds
  happening at the same time";
- "non starvation of newly sent messages while old stuff is syncing";
- "very large communities too".

## Where it stands

| | |
|---|---|
| The world and the network | built: engine/world/World.lean, Fair.lean |
| Statements | 42, each a closed `Prop` with no `sorry` (engine/world/Statements.lean), audited |
| Proven of the running code | **the pilot, `claim_delivers_stmt`** (`pilot`); `grows_stmt` (`grows_all`); the node invariant in every reachable world (`reach_ok`); the three hops of a round's leg (`claim_wants`, `want_sends`, `op_taken`); the walk's laws of main's `walkN` (`walk_proof`) |
| Proven above the code | the reduction `edge_stmt → grows_stmt → converge_stmt`; from it, T-converge for 2, 3 and n peers, all-know-all and transitive; T-op, T-offline; chains, stars and webs, with their diameters |
| False on today's code | `session_stable_stmt` (finding 1), `rooms_stmt` and `join_stmt` (finding 2): node-level witnesses in Lean. `fresh_stmt`: argued ("T-fresh" below), no Lean witness yet |
| The open core | `edge_stmt`: per-edge progress. Every T- law above reduces to it and to growth |

## Decisions

- **One world, n nodes, the running code.** `World` holds n real
  `Node`s, each on a box of state that a pure run of its monad threads,
  and the network as data. There is one step function. a3's two-node
  world and the pair-secrecy world are instances of it (below).
- **Every way in is a step, and only those.** The steps are: deliver,
  duplicate, drop, tick, a user's write through `Node.onWrite`, crash
  and restart, the harness's `connect`, and the attacker's injection.
  Nothing else changes a node, so an app write that bypasses the node
  is outside the world, and `index_store_stmt` says what it breaks.
- **The plain world's rooms are read from the store.** `Plain.rooms i h
  cid` is the trust rule as data: fixed rooms ignore the store, while a
  stored admission adds a room and a stored removal takes one away. So
  joins, removals and rooms that differ at a session's two ends are
  statable without the Connection family.
- **The network is a record of parameters** (`Net`): the knows-graph,
  per-node `online`, per-link `link`, `gst`, Δ, τ and ρ. An execution
  the network may produce is `Net.Admits`. Every liveness law names it;
  nothing about schedulers is built into the world.
- **Liveness is bounded progress, never a bare "eventually".** Every
  liveness law says "within T ms", with T an explicit function of the
  parameters: `epoch` per edge by rounds, `hop = 3Δ` per edge by the
  stream, and d times either across d edges. So the liveness proofs are
  latency bounds too.
- **Liveness rests on rounds; the stream is latency.** The per-edge
  bound cites only rounds. The stream is proven separately
  (`relay_stmt`, `fresh_stmt`), so an optimization that fails can cost
  time, never convergence.
- **Per op, not quiescence.** `op_stmt` and `converge_stmt` hold while
  writes go on. Only `quiescent_stmt` (the whole community, by a
  potential) assumes writes stop.
- **Node code must be provable.** No `while` or `partial` in anything a
  node runs (finding 3), and no tactic run on a program that is not yet
  known (finding 5).

## The world

engine/world/World.lean.

```
World S n = { node : Fin n → Node, box : Fin n → S,
              flight : List Packet   -- in flight, in send order; any may go next
              wire   : List Packet   -- everything sent (the attacker's view)
              now, serial, wrote, delivered }
Packet    = { serial, src : Option (Fin n), origin, dst, bytes, sent }
Setup     = { n, sync : Fin n → Sync F M, addr, run, held, floor, crash,
              harness, honest, peek }
Plain F   = { fam, cfg, n, addr, rooms : Fin n → Held F → Id → List Id }
```

- **A step runs one entry point** (`World.enter`). The node and its box
  move on, and the node's `Effects.send` become packets in flight and on
  the wire, each with a fresh serial, its sender, the sender's address
  and the time.
- **Delivery** removes one packet from `flight` (by index) and runs
  `Node.onFrame` at the node whose address is its `dst`. A packet to no
  node is lost.
- **Duplication** copies a packet in flight with a new serial and no
  sender. **Drop** removes one. Delivery in any order is reordering.
- **Restart** keeps the box's store (`Setup.crash`) and boots the node
  from its log: sessions, rounds and everything else in memory are gone.
- **Injection** runs `Node.onFrame` on bytes the attacker can make
  (`adv`): nothing (`noAdv`), anything, or pair-secrecy's Dolev-Yao
  `Deliverable` over `wire`.
- **`Legal`** gates acts: time never goes back (`step_now`,
  `Exec.now_mono`), a named packet is in flight, a user writes only what
  `honest` allows, `connect` only in the harness, injections only what
  `adv` allows.
- **Executions** are infinite legal sequences (`Exec`); `Reachable` is
  the finite prefix closure, for safety.

**The plain world** (`Plain`, with `setup`, `start`, `Reach`, `Run`,
`Holds`): n nodes on held stores, frames in the clear (`plainSeal`), no
handshake (sessions come from `connect`), and rooms read from the store.
It is where liveness is proven first.

**The Connection world** (next): the Connection family's real hooks, so
the trust rule gives the rooms; handshakes make sessions; sealed frames;
a box with entropy (`NodeM`).

### The two existing worlds, as instances

- **a3/world** (`World`, `World.Step`, `stream_delivers`,
  `stream_offered`, `conn_answers_ids`) is `Plain` with n = 2, `Who ≅
  Fin 2`, and constant rooms.
  - `World.Step S w w'` is `∃ a, Legal … noAdv w a ∧ w' = w.step _ a`,
    delivering by index instead of a `pre ++ f :: post` split.
  - a3's per-entry-point lemmas (`write_offers`, `hold_wants`,
    `want_sends`, `op_taken`, `seal_mem`) are about `Node` on `HeldM`
    and port unchanged; Run.lean already carries the loop and `Keeps`
    machinery, now with `concrete_goal`.
  - `stream_stmt` is `stream_offered` for every step, not only writes.
- **fd/pair-secrecy** (`Pair.World`, `Act`, `Setup.Step`/`Run`) is the
  Connection world with n = 2.
  - Its `deliver` (any `Deliverable` bytes from any source) is the
    unified world's `inject` with `adv := Deliverable`; honest delivery
    hands over bytes already on `wire`, which are always `Deliverable`.
    So every law proven against the attacker-only world holds here.
  - Its steps put no order on time; ours do. Our executions are a subset
    of its, so its safety laws hold of ours unchanged.
  - `PairOnly` stays a per-step environment hypothesis; `opened` is a
    ghost field the port adds.
  - `secrecy_stmt`, `authentic_stmt`, `frameReplay_stmt`,
    `bareReplay_stmt`, `deadDropped_stmt`, `heard_stmt`,
    `forward_stmt` and `live_stmt` keep their statements.

This unification goes to holmes-a3 for review before it replaces
a3/world.

## The network we tolerate

engine/world/Fair.lean, `Net`:

| parameter | meaning |
|---|---|
| `G` | the knows-graph: who knows, and trusts, whom |
| `online t i` | node i is up at time t; on a phone, the app is in the foreground |
| `link t i j` | the link is up; a partition is a link down, healing is it coming back |
| `gst` | when partial synchrony begins |
| `Δ` | from gst, a packet across a live edge of G arrives within Δ |
| `τ` | from gst, an online node ticks at least every τ |
| `ρ` | from gst, two online neighbours on a live link have a session within ρ |

- **Before gst, anything.** Loss, duplication, reordering, any delay,
  partitions and dropped sessions are all steps the world allows.
- **`Net.Admits E`:**
  - nothing runs at an offline node and nothing is delivered to one;
  - from gst, `timely`: a packet an honest node sends across a live edge
    is delivered within Δ (so not lost);
  - `ticks`, `redial`, and time passes.
- **The liveness hypothesis is partial synchrony after gst, with 2Δ <
  patience.** It is the formal content of H-fair(K). **The user has not
  approved it yet.** Everything below builds on it; replacing it changes
  only `Net.Admits`.
- **Sessions are assumed to come back** (`redial`). Session stability
  and handshake liveness are separate statements, so the hypotheses
  only shrink: in the plain world, `session_stable_stmt` after the
  patience fix; in the Connection world, "two trusting, ticking nodes
  end up with a session".
- **Rooms are a separate premise per room**, since they change:
  - `Carries E G r k₀`: from k₀, every session between neighbours shows
    the same rooms at both ends, r among them. Today's code needs the
    equality (finding 2).
  - `Shares E G r k₀`: r at both ends, the rest free. This is what
    `rooms_stmt` says should be enough.
- **A FIFO link with a bandwidth** (`Fifo`, for `fresh_stmt`) refines
  `timely`: a packet arrives within Δ plus the time the bytes queued
  ahead of it on its link (`ahead`) take at `bw`.
- **`Fair Q N E W`** bundles the rest: `PlainOk`, symmetric G,
  `N.Admits E`, 2Δ < patience, every window within W items, and the two
  collision assumptions (`Unclashed` for op ids, `FpSound` for range
  fingerprints).

## Statements

engine/world/Statements.lean. Status: **P** proven, **R** reduced to
`edge_stmt` (and growth) by a proven implication, **F** false on
today's code (with the finding), **O** open.

### L: the running code, over every reachable world

| statement | says | |
|---|---|---|
| `grows_stmt` | no step, against any attacker, takes a shared op out of a store | **P** (`grows_all`) |
| `index_store_stmt` | the room index names exactly the stored ops of each room | **P** (`index_store_proof`) |
| `stream_stmt` | a stored op is offered at once on every session that shows its room | O (a3's `stream_offered` for writes) |
| `offered_stmt` | L-offered: both | O |
| `members_only_stmt` | session frames carry only ops of rooms the session showed in that step | O (ConnLaws per entry point) |
| `frames_keep_sessions_stmt` | no delivery, duplicate, injection or write closes a session | O |
| `idem_stmt` | L-idem: the same bytes delivered again leave the store as they were | O |
| `restart_stmt` | L-restart: a restart keeps every op, rebuilds the index equal to the store, opens nothing | **P** (`restart_proof`) |
| `waiting_closure_stmt` | every store at rest, verdicts = spec | O (engine laws + Held's turn) |
| `closure_agree_stmt` | holding a closure, judge alike | O (`spec_local`) |
| `local_stmt` | L-local: the same ops give the same verdicts and every view the same answer | O |
| `round_stmt` | L-round: a round carries both sides' ops within `roundTime`, whatever interleaves | O; the pilot is its first leg |
| `round_forward_stmt` | L-round's forward leg, leaf regime: every op of the window i's index named at the opening reaches j within 3Δ | **P** (`round_forward`, from the pilot) |
| `round_ends_stmt` | L-round-terminates: a round ends at both ends within (D+1)Δ | O |
| `no_false_settle_stmt` | L-no-false-settle: "settled" means holding the peer's snapshot of the window | O |
| `dup_concurrent_stmt` | L-dup-concurrent: frames keep sessions, idem, and `round_stmt` | O |
| `session_stable_stmt` | a joined session over a live edge is never dropped | **F** (finding 1) |
| `claim_delivers_stmt` | the pilot: a claim listing x, from i to j → j holds x within 3Δ | **P** (`pilot`) |
| `walk_stmt` | the walk keeps the store, touches only frontier/offered/closed, is idle on an empty frontier | **P** (`walk_proof`, of main's `walkN`) |

### T: many nodes over time

| statement | says | |
|---|---|---|
| `edge_stmt` | per edge: an op one end holds, the other holds within `epoch` | **O: the core** |
| `op_stmt` | T-op: down any path of d live edges, within d · epoch, under continuous writes | R (`op_of`) |
| `converge_stmt` | T-converge: diameter d, everyone, from some step on, within d · epoch | R (`converge_of_edge`) |
| `converge_all_stmt`, `converge_two_stmt` | everyone knows everyone; two peers: one epoch | R |
| `converge_three_stmt` | three peers on a chain: two epochs | R |
| `quiescent_stmt` | the whole community: no writes, the potential falls to 0 within d · epoch | O |
| `offline_stmt` | T-offline: back from offline (crashed or not), catch-up and outbox, at one step, within d · epoch | R (`offline_of`) |
| `closure_stmt` | T-closure: every node judges every op alike within d · epoch | O |
| `join_stmt` | T-join, raced and relayed: a joiner gets everything and is heard within (dM + 1) · epoch | **F** today (finding 2: rooms differ until J holds its admission) |
| `remove_stmt` | T-remove, the transport bound: nothing u writes after its neighbours hold the removal enters any store | O |
| `read_stmt` | T-keys / T-read: a view local to closures reads the same everywhere within d · epoch | O |
| `files_stmt` | T-files: every chunk of a file, everywhere, within d · epoch | O |
| `rooms_stmt` | T-rooms: a room both ends show syncs whatever else they show | **F** (finding 2) |
| `rooms_concurrent_stmt` | T-rooms-concurrent: rooms that come and go, each from when it is carried | O |
| `relay_stmt` | T-relay-concurrent: the stream down a path, d · 3Δ, with relays busy both ways | O |
| `churn_stmt` | T-safe-churn: all safety laws under every interleaving of churn | O (its parts) |
| `fresh_stmt` | T-fresh: a fresh write reaches a neighbour within a bound independent of backlog | **F**, argued (below); no Lean witness yet |

### Topologies and bounds

| statement | says | |
|---|---|---|
| `chain_stmt` | a chain of n: n - 1 epochs end to end | R (`chain_of`, `diam_chain`) |
| `star_stmt` | a star: two epochs | R (`star_of`, `diam_star`) |
| `web_stmt` | any web: the source's eccentricity in epochs | R (`web_of`) |
| `lower_stmt` | at least δ per hop if every packet takes δ: a node d edges away holds x no earlier than d · δ | O |

The upper and lower bounds match up to a constant per hop:
- by the stream, 3Δ per hop against δ = Δ: an offer, a want, the op;
- pushing a fresh op whole would be Δ per hop, at the cost of
  duplicates. That is a design question, below.

### Scale

| statement | says | |
|---|---|---|
| any G | every T- law above holds over any knows-graph, the bounds in its diameter d | R |
| `work_stmt` | at rest, a node of degree D showing R rooms sends at most c · D · R · (1 + T / every) packets in T ms, whatever n | O |

## Proven today

- **Over the running code** (given `walk_stmt`):
  - the pilot, `claim_delivers` (below);
  - `reach_ok`: every node of every world the plain world reaches keeps
    `NodeOk` (its index names exactly the stored ops of each room, its
    snapshots name stored ops, no family sessions, ops filed under their
    ids, the log exactly the store), against any attacker, over every
    entry point and restart; so `index_store_proof` and `restart_proof`;
  - `reach_flight`: every packet in flight was sent no later than now,
    and an honest one says it came from its sender's address;
  - `grows_proof`: shared stores only grow;
  - the hops, at a node, over frames of any payloads: `claim_wants`
    (H1), `want_sends` (H2), `op_taken` (H3);
  - closed forms of the node's steps on a held store: `write_run`,
    `store_run`, `fanout_run`, `apply_run`, `finish_run`,
    `onFrame_sealed`, `onTick_run`, and `seal_mem`;
  - the findings' witnesses.
- **Above the code, from the per-edge bound** (engine/world/Epidemic.lean):
  - `hops`: d · B over a path of d live edges;
  - `converge_of_edge`, `converge_all_of`, `converge_two_of`,
    `converge_three_of`;
  - `op_of`, `offline_of`, `chain_of`, `star_of`, `web_of`;
  - `diam_chain`, `diam_star`, `diam_allKnow`, `step_now`,
    `Exec.now_mono`.

So the whole T-converge family, chains, stars, webs and T-offline hang
on one lemma about one edge. That lemma is the program's core, and the
pilot is the first third of its round.

## The pilot

**Proven: `pilot : claim_delivers_stmt`** (engine/world/Pilot.lean),
from `claim_delivers : walk_stmt → claim_delivers_stmt` and `walk_proof`. In words: in any execution of the plain world
that the network admits, a round's claim of ids, in flight from i to j
on a session joined from then on, both of whose ends show room r, that
lists op x of r which i holds, gets x to j within 3Δ of the claim's
sending. Any number of nodes, sessions, rooms and other frame payloads
may surround it, and any other steps may interleave.

The proof is an obligation chain over three hops, each one lemma about
one entry point run on any state that keeps the node invariant:

1. The claim arrives within Δ (`timely`). If j holds x by the end of
   that frame, done. Otherwise x is in no snapshot j keeps (snapshots
   name stored ops), so j's answer wants x, in a frame back to the
   claim's sender, which is i's address (`claim_wants`, `reach_flight`).
2. The want arrives within Δ. i still holds x (`grows_proof`), in a room
   the session shows, so i sends x's bytes back (`want_sends`).
3. x arrives within Δ, and j stores it (`op_taken`). It is filed under
   its id (`NodeOk.ids`), so j holds x in room r (`Unclashed`).

Negative controls, each run and reverted (not committed):
- `Conn.onWant` sending none of the wanted ops: `onWant_sends` fails,
  so H2 and the pilot do not build;
- `Conn.onRbsr` dropping the first id it wants: `onRbsr_wants` fails,
  so H1 and the pilot do not build.

What the pilot assumes, beyond `Fair` and the session:
- nothing about the walk any more: main's `walkN` has its laws (`walk_proof`);
- the session's rooms are fixed at both ends (`∀ h, r ∈ Q.rooms i h
  cid`). Dynamic rooms need rooms to be monotone in the store within a
  step, a premise for the dynamic-trust work.

The pilot takes any round message one of whose claims lists ids, so the
forward leg of a round follows: `round_forward` proves that every op of
the window that i's index named when the round opened reaches j within
3Δ, in the leaf regime (the index is the store, `index_store_proof`).

What is still open for `round_stmt` in the leaf regime:
- the reverse leg (j's ops to i: an offer in the answer, i's want, the
  op), with the `asked` invariant for an offer whose want went earlier.
  a3/sync-harden changes `asked` (bounded, deferred, expiring), so this
  waits for it to land;
- a non-vacuity witness: a concrete fair execution satisfying the
  premises.

## T-fresh: where fresh ops queue behind backlog

The user saw new messages starve while old ones synced. In the model,
Δ is per packet and nothing queues, so the stream gives 3Δ per hop
whatever is in flight. The starvation lives in what Δ hides. Here is
where today's send path puts a fresh op behind a backlog, in order:

1. **The runner's one event channel** (engine/wire/Tcp.lean,
   `runLoop`). The app's `Runner.write` is an event on the same FIFO
   channel as every frame read from every socket. A local write waits
   for every frame already queued. Each frame is a bundle of up to
   `bundle` = 48 KB of payloads, and each op in it is its own write
   turn on SQLite.
2. **Blocking sends** (`RunState.apply`, `sendOn`). Each payload is
   sent with `.block`, so the loop waits for the kernel to take it.
   - On a slow link, one large answer stops the whole node: other
     sockets, ticks and writes.
   - A fresh offer is written after every byte already handed to that
     socket (TCP's FIFO).
3. **Answers are unbounded in bytes** (`Conn.onWant`). One want names up
   to `maxIds` = 4096 ids, and all the ops found are sent in that one
   step. A frame may carry several wants. A round that finds a large
   difference therefore puts megabytes on the socket at once, and a
   fresh offer queues behind all of them.
4. **The closure walk** (`Conn.walk`) offers up to `walk` = 100000 ids
   per call. The peer's wants for them come back as more bulk answers.
5. **The receiver processes in order.** A fresh offer that arrives behind
   backlog frames on the same socket waits for all of them to be taken
   (point 1). Its want then queues behind the receiver's own outgoing
   answers (point 2).

Nothing in `Node` or `Conn` reorders: a step's payloads go out in the
order the step produced them, and a fresh op's offer is always in a later
step than the backlog already sent. So there is no starvation inside the
protocol. It is all head-of-line blocking in the transport and the
runner, and the backlog can be made arbitrarily large (point 3).
`fresh_stmt` is false with any fixed B: put m wants of 4096 large ops
just before the write, and the delay grows with m.

**A fix that makes `fresh_stmt` provable** (for holmes-a3, who owns
Conn, Node's send path and Tcp):
- per session, two classes of payload:
  - urgent: wire control (rbsr, have, want), ops a local write just
    stored, and ops wanted right after a fresh offer;
  - bulk: answers to round wants;
- each step sends every urgent payload first and at most `burst` bytes of
  bulk; the rest carries to the next tick;
- the runner gives local writes their own channel, read before frames,
  and gives each socket its own writer task, so a send never blocks the
  loop;
- then the bytes ahead of a fresh offer are at most `burst` plus one
  frame, and `fresh_stmt` holds with B = 3 (Δ + (burst + maxFrame) / bw).

## Findings

Each finding is a statement above that is false of today's code, or a
rule the proofs need. Witnesses are in engine/world/Findings.lean.

1. **Patience counts from the last receipt, not from the wait's start**
   (`patience_drops_idle`).
   - A dialer's idle session opens a round at its cadence tick t. If
     the peer was last heard patience or more before t, the next tick
     drops the session, unless the answer has already come.
   - With the defaults (rounds every 30 s, patience 20 s, a tick every
     200 ms), every idle session is dropped at its next cadence round
     whenever the round trip takes longer than one tick.
   - So `session_stable_stmt` is false for every Δ above the tick.
   - Convergence survives it: a new session's first round opens at the
     hello, with `heard` fresh, so with `redial` every edge still gets
     a full round. The cost is a session torn down and redialed per
     cadence round on slow links.
   - Fix: one field, `heard := now` in `Conn.start`.
2. **A room shown at only one end stops every round on the session**
   (`unshown_unanswered`, `no_round_while_open`).
   - The answerer sends nothing for a round in a room it does not show.
   - The dialer waits on that round forever and opens no round in any
     room meanwhile, until patience drops the session.
   - Rooms differ whenever one end has stored an admission the other
     lacks, which is every join.
   - So `rooms_stmt` and `join_stmt` are false, and `Carries` must
     assume equal rooms.
   - holmes-a3's `uncarried_room_answered` addresses this. Two possible
     fixes: answer with an empty claim list, which ends the round; or
     name the shown rooms in the hello.
3. **`while` is opaque to proofs** (fixed on main by a3/hostile's
   structural `walkN`). What the laws need of the walk is `WalkLaws`
   (keeps the store, touches only frontier/offered/closed, idle on an
   empty frontier), proven of `walkN` by induction on its budget
   (`walkN_laws`, `walk_proof`).
4. **Snapshots are per room, not per round** (observed, not proven).
   - `onRbsr` drops every snapshot of room r on any message of r. So a
     duplicated empty message of an old round ends the current round at
     the dialer early.
   - The round continues from the live index, which only grows. That is
     harmless for liveness, but `exchange_complete`'s fixed-snapshot
     premise does not hold under duplication.
   - The first round, the one `no_false_settle_stmt` is about, has no
     older round, so settling is unaffected.
5. **A tactic run on an unknown program never stops.** The 70 GB `lean`
   of 05:15 was this.
   - Plain.lean's `write_sub` passed `forIn_at _ _ (turnH fam _ h) …` to
     `obtain`, so the loop body was a metavariable when its
     `by keeps []` ran.
   - `keeps` (and `grows`) apply `Keeps.bind'` under `repeat'`. On
     `Keeps (?f a b)` each application makes `?f` a bind of two new
     unknowns, forever.
   - A six-line repro reaches 4 GB in under a minute.
   - Fix: both tactics now refuse a goal with metavariables
     (`concrete_goal`), and `write_sub` is proven from `write_run`, a
     closed form. The World library builds in seconds under a 16 GB cap.
   - Rule: state the loop or the call first, then prove `Keeps` of it.

How the earlier bugs map onto the statements:

| bug | what catches it |
|---|---|
| app writes bypassing the node, never offered | `index_store_stmt`: the only write step is `onWrite` |
| a replayed purged request killing a live session | `frames_keep_sessions_stmt` here; pair-secrecy's `bareReplay_stmt` in the Connection world |
| `Conn.tick` measuring patience from the last receipt | `session_stable_stmt` (finding 1) |
| a one-sided room's rounds never answered | `rooms_stmt`, `join_stmt` (finding 2) |
| new messages starving behind old | `fresh_stmt` |

## Composition with holmes-a3's laws

holmes-a3 is writing step-bounded Conn laws after a3/hostile, and RBSR
cost bounds over a shared `Budget` record. Where they plug in:

| a3's law | discharges |
|---|---|
| `walkN` and its laws | `walk_stmt`: done on main (`walk_proof`) |
| `tick_drop_iff`, `round_not_dropped` (with the patience fix) | `session_stable_stmt`, and so `redial`'s role in the per-edge bound |
| cadence | `gap`: the dialer opens a round within `every + (D+1)Δ + τ` |
| `uncarried_room_answered` | finding 2, so `rooms_stmt`, then `join_stmt` |
| RBSR cost bounds over `Budget` | `depth cfg W` from 2W + 1 to 2⌈log_fan W⌉ + 2; `W` becomes a `Budget` field |
| `have_shown`, `hold_reply_local` | `Msg.hold` gains its room: the pilot's hop lemmas and `stream_stmt` read `Msg.hold r L` |
| `sealed_auth`, `onFrame_sealed` | the Connection world's frame hops |

`edge_stmt` decomposes as: a session within ρ (redial, or stability),
then a round within `gap` (cadence), then `round_stmt` within
`roundTime`. Only the last piece is this branch's.

## Large communities: design questions

These are listed, not decided.

1. **Who dials whom.** A full mesh is n - 1 sessions per node. The bounds
   need only a connected overlay of small diameter. Which overlay
   (random regular, a ring with chords, by room), and how is it kept
   connected as members come and go?
2. **Duplicate wants.** `asked` is per connection. A node offered x by D
   neighbours at once wants it from all D and takes D copies. Should a
   node keep one set of ids in flight, with a timeout to ask elsewhere?
3. **Push or pull for fresh ops.** The stream costs 3Δ per hop (offer,
   want, op). Pushing small fresh ops whole costs Δ per hop but sends D
   copies to each node.
4. **Cadence and degree.** Idle work is D · R round openings per `every`
   (`work_stmt`). Should `every` grow with D, or should rounds open only
   on sessions with recent changes?
5. **Window size.** Claim depth grows with W. With 2W + 1 today, a large
   window makes the per-edge bound linear in W until the log bound is
   proven. Snapshots cost O(D · R · W) memory per node.
6. **Rooms per session.** One session carries every room both ends show.
   A finding-2-style stall in one room stalls all of them.
7. **The closure walk's budget** (100000 ids per call) is a burst of
   bulk, which T-fresh's fix must pace.

## What stays assumed

- **Crypto.**
  - SHA-256 has no collision on the ops an execution carries
    (`Unclashed`, giving `Distinct`), nor on the fingerprints' labels
    (`FpSound`).
  - Ed25519 is unforgeable, for the membership laws the trust rule
    reads.
  - In the Connection world, the symbolic Noise and AEAD (pair-secrecy's
    `Ideal`, `Apart`).
- **The network is a hypothesis, not a model of TCP.** The world's
  packets are what the runner's sockets carry. That the runner does
  this is tested by tcppair and jointcp, not proven. Nothing assumes
  TCP's ordering, except `Fifo`, which only `fresh_stmt` uses.
- **Partial synchrony after gst** (`Net.Admits`), not yet approved by
  the user.
- **Clocks.** Each node's `now` never goes back. Nothing relates two
  nodes' clocks: Δ and τ are in the world's time, and a node's patience
  and cadence are read from its own.
- **The seam calls only the entry points.** Platforms write through
  `Runner.write` and nothing else. This is a code property, tested,
  with a CI check to come.
- **SQLite behaves like `Held`.** The differential and crash tests check
  this, as for every engine law.
- **Lean's kernel, compiler and runtime.**

## How a law about running code is proven

engine/world/Run.lean:

- **Running code on a held store is rewriting.** `HeldM.run_bind`,
  `run_pure`, `run_getOp` and `run_turn` reduce a do block's run to a
  term. A loop whose turns only yield is a fold (`forIn_yield`).
  `write_run` is `Node.write` so.
- **Most code only reads** (`Keeps`, `Grows`). The `keeps` and `grows`
  tactics prove it from a do block's structure, on a goal with no
  metavariables (`concrete_goal`).
- **Loop invariants:** `forIn_inv`, `forIn_hoare`, `forIn_at`.
- **Hop lemmas** say: delivering a packet of this shape, to a node in
  any state satisfying the world invariants, puts a packet of the next
  shape in flight.
- **World invariants** are proven once per entry point and lifted by
  induction over `Reachable`.

Rules for node code and its proofs:
- no `while`, `repeat` or `partial` in what a node runs;
- hooks only read, or write through `Turn`;
- every change to a node goes through an entry point;
- never run `keeps`, `grows`, `simp` or `split` on a goal whose program
  is a metavariable: state the call first;
- build under the cap: `systemd-run --user --scope -p MemoryMax=48G -p
  MemorySwapMax=0 lake build World`.

## Next, in order

Rough sizes are lines of Lean.

1. **The reverse leg and the opening** (j's ops to i: offer, want, op,
   with the `asked` invariant; the dialer's opening lists its window),
   about 300, reusing the hops. Then `round_stmt` in the leaf regime.
2. **The patience fix and `session_stable_stmt`**, with a3's
   `tick_drop_iff`, about 300.
3. **The cadence lemma (`gap`)**, with a3's cadence law, about 200.
   Then `edge_stmt` in the leaf regime, and with it every R row above.
4. **Claim trees**, about 800: fingerprint hops as obligations measured
   by `exchange_ends`; with a3's cost bounds, the log depth.
5. **The remaining safety statements**, about 500 now that the closed
   forms exist: `index_store`, `stream`, `members_only`,
   `frames_keep_sessions`, `idem`, `restart`, `waiting_closure`,
   `closure_agree`, `local`.
6. **T-fresh**, after a3's send-path fix, about 400: `ahead` bounded by
   `burst`, then the 3-hop latency under `Fifo`.
7. **Dynamic trust**, size unknown: `rooms_stmt` after finding 2's fix,
   then `join_stmt` and `remove_stmt`; the Connection world's
   `Plain.rooms` from the trust rule.
8. **The Connection world**, about 400 to port pair-secrecy's laws onto
   it, then handshake liveness (about 1000).
9. **Non-vacuity witnesses** for the liveness laws: a concrete fair
   execution (round-robin schedule, every packet delivered at once),
   about 300.
10. **A CI check** that only engine/core and engine/wire call `Turn`,
    `receive` or `Store.putOp`, about 30 lines of script.
