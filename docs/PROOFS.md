# The n-node World: convergence over running code

The user's target (2026-11-01): **whenever we connect or reconnect or send
a message, sync happens in bounded steps, whoever is sending or
connecting.** That is a per-link statement, `Edge` (engine/world/Fair.lean),
symmetric in who dials or writes. Convergence over any web of members is
its corollary (`Plain.converge`, `Plain.offline`).

## The World (engine/world/)

- **World.lean**: n nodes, each the running `Engine.Sync.Node`, on held
  stores, with the network as data. Acts: deliver, duplicate, drop, tick,
  write, restart, transport close, the harness's connect, and the
  attacker's injection. The plain setup runs a3's `Setup.sync` at every
  node (fixed rooms, frames in the clear), so a3's node laws apply as
  they are.
- **Fair.lean**: the network we tolerate (`Net`, `Net.Admits`: from gst,
  timely delivery across live edges, ticks, redials) and the boundary
  `Edge`: across a live edge, an op one end holds, the other holds within B.
- **Epidemic.lean**: webs, chains, stars, three peers and offline
  catch-up, from `Edge` and growth, for any execution and any B.
- **Plain.lean**: `grows`, i.e. shared stores only grow in every execution
  against any attacker, on main's `entry_fresh` (a turn only adds ops, and
  a purge takes only ops of no room).
- **Hops.lean, Asks.lean, Owed.lean**: the three hops of an op across a
  session, over frames of any payloads, at a node with any sessions:
  - H4 `onSealed_wants`: a have of an unasked op is answered with a want;
  - H2 `onSealed_queues`: a want of a held op queues it or sends it;
  - H3 `onSealed_takes`: an op of a shown room is stored.

  Each runs the real `onSealed` loop. The other payloads in a frame may
  ask, queue or store anything; the laws track them through the loop.
- **Inv.lean**: invariants of every node in every execution
  (`managed_nil`).
- **Link.lean**: the hops at a delivery (`deliver_wants`,
  `deliver_queues`, `deliver_takes`): what the step does at the node the
  packet reaches, and what it puts in flight back.

## Premises the laws take, and why

- **Asks room** (finding 7): the session's asks have room for every id the
  frame offers (`asked + Σ asksOf ≤ maxKnown`). With no room, `admitAsks`
  drops the want, and nothing re-asks until a round or retry names the id.
- **Queue room**: the session's queue has room for every id the frame
  wants (`owed + Σ wantsOf ≤ maxKnown`), and owes nothing outside it.
- **The index lists the op** (H2's `authorize` reads the index, not the
  store). Being discharged as a World invariant (index ⊇ store).
- **No hash collision** among the ops a frame and the store carry.
- **S1, trusted transport** (approved by the lead): no loss without a
  close, and no duplicates; order is arbitrary, since lanes reorder.
  - The S1 audit found the runner breaking it: ordinary-lane overflow
    dropped batches with no close (F1).
  - The fix is on `fd/overflow-close`.

## What a send costs (the send half of `Edge`)

- **A fresh write:** 3 hops (have, want, op). The want is served at once:
  the writer's op is hot, and `hotOf` serves one hot id per service, ahead
  of the queue.
- **Any other op:** 3 hops plus the sender's owed backlog, i.e. up to
  ⌈bytes owed ahead / burst⌉ serve turns. Main's `owed_within` bounds it
  by the op's queue position.
- **Relayed ops are not hot** (only `onWrite` heats). So along a chain of k
  peers a new message takes about 3k hops only when relays' queues are
  empty. Fresh relays become hot on `fd/relay-hot` (stream-asked ops only;
  own writes keep strict priority).

## Gap list: plain World → the running app

| Gap | What closes it |
|---|---|
| Sessions from the harness's `connect`, frames in the clear, fixed rooms | The n-node World with the Connection hooks (sealed sessions, the handshake, rooms from the store): holmes-71's session forms, stated over this World's `Net`/`Live`, discharge `Net.Admits.redial` and `Carries` |
| `Edge` not yet discharged | Chain the hops over time (timely delivery), the queue's drain at ticks, the reconnect/safety round (item 2's live-round law, fd/live-rounds) |
| Index ⊇ store, owing ⊆ owed (premises) | World invariants over every execution (in progress) |
| No catalog sweep in the plain World | The Connection hooks' catalog; not on the per-link path |
| Purge | Never runs in the plain World (its hooks give no secrets or couriers); purges take only room-less ops, so `grows` holds with them too |
| TCP and the runner | S1 as an assumption, audited against Tcp.lean (status-3.md, "S1 transport audit") |

## Not ported from fd/proofs, and why

- **Snapped/SnappedAt/TreeCalm/RoundCalm (Tree.lean, Calm.lean), Round.lean,
  Leaf.lean:** superseded by event-driven live rounds (item 2). There are
  no per-round snapshots to keep calm. The claim-tree chain is to be
  restated on item 2's `live_discovers`.
- **Findings.lean:** findings 1, 2, 3 and 10 are fixed on main (sync-harden,
  `room_independent`, structural `walkN`, settle deleted).
- **Plain.lean's per-entry-point growth (614 lines):** replaced by main's
  `entry_fresh` and two facts about turns and purges.
- **Members.lean:** main's `entry_fresh` (`FramesOk`) states what every
  frame carries, per node. An n-node lift is later; it is not on the
  per-link path.
- **Settle.lean, Idem.lean:** not on the per-link path. Later.
- **Statements.lean:** the statements that remain are stated as theorems
  over `Edge` (Epidemic), and the rest wait on the per-link discharge.
