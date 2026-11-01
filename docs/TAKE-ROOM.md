# Take rooms: what a session carries before admission

## The finding

The trust rule (`Connection.trusts`, app/community/Commands.lean) has
two clauses. `allowPeer c peer` takes a key a live device of c is
admitted under. The link clause (`linked`) takes, before this node is
let into c, the inviter key a pending join names, if this node knows no
admission under it. Anyone who knows c's id can make a link naming their
own key. `roomFor` used to turn either clause into `Room.sync c`, synced
both ways, so a node not live in c that opened such a link synced all it
held of c to that key: a removed member's node, its whole history.
Bodies stay sealed; admissions, names, reactions and wraps went across.

The engine could not say "take, but do not show": a `Conn` had one room
list, governing both directions.

## The rule

A node that is not live in c sends no op of c on a session whose peer
only the link clause lets in. It still takes c from that peer, so a
joiner learns of its admission. Its join request needs no session: it
travels in the hello (`dialOne` seals `hello c listen [jr]`; the inviter
stores it through `deliverAll`/`joinsOf`).

`roomFor` (app/Commands.lean), where this node is a device of c:

| the peer | carried |
|---|---|
| `allowPeer c peer` | `Room.sync c` |
| only the link clause (`linked c me peer`) | `Room.take c` |
| neither | a notice of each removal owed to the peer's key, not yet given |

The handshake's trust rule is unchanged: the session opens; what it
carries changed.

## The take room (engine/sync)

`Room.take r` (Notice.lean) sets `Conn.takes` (Conn.lean) beside
`rooms`, by `setRooms`/`carry`; a room both synced and taken is synced.

- **Taken:** `recv` hands the writer a data op of a shown or taken room.
- **Wanted:** `onHold` answers haves for `rooms ++ takes`, wanting the
  ids this side lacks (it reads this side's ops of that room only).
- **Rounds:** `start` and `ask` iterate `rooms ++ takes`, so a take room
  is due like any other. Its rounds open and answer through the same
  interface from the empty index (`Conn.view`): an opening is one
  `.ids q []` per window range; a fingerprint is answered `.ids q []`
  (or settled if it names nothing); an id claim is answered with wants
  for its ids, and no claim back.
- **Never shown:** `shows`, `filed`, `authorize`/`onWant`, `serveOwed`
  and the closure walk read `rooms` only, so nothing of a take room is
  offered, served or streamed.
- **Round state** (`active`, `rounded`, `epochs`, `short`) is keyed by
  room and bounded by `rooms.length + takes.length`. A room's opening
  record is kept only while it stays synced, or stays taken: a joiner's
  room that turns synced is due at once (`shown_due`).

No wire change: the empty id claim is the bytes a synced room sends
for a range it holds nothing in. The peer that syncs c answers a take
room's opening by ending the round and offering, as haves, every id it
holds in the window (`take_round_offers`).

Cost: per round, a take room sends one claim per window range and the
wants; the peer sends a have per id it holds in the window, every
`safety` while the room stays taken (until the joiner holds its
inviter's admission).

## Laws

Engine (engine/sync/TakeLaws.lean; restated: `recv_take`, `recv_cases`,
`hold_reply_local` over the carried rooms, `notice_no_holds`,
`unshown_room_answered` for a room neither shown nor taken,
`RoundBounded`, `conn_state_bounded`):

- `take_unshown`: an op of a room not shown is not shown.
- `start_take_blank`, `onRbsr_take_blank`: a take room's rounds claim
  only empty id lists and send no have.
- `take_opens`: a due take room opens.
- `take_round_offers`: the syncing peer offers all it holds there.
- `recv_takes_taken`: a take room's op received is taken.

App (app/Proofs.lean):

- `roomFor_law`: each room `roomFor` gives, read from the code: synced
  only where `allowPeer` takes the peer; taken only where `allowPeer`
  refuses it and the link clause takes it; else an owed notice.
- `rooms_take`: a take room means this node is not live in c
  (`linked_unlive`) and a peer only the link lets in.
- `rooms_removed`, `rooms_cut`, `rooms_cut_node`, `refused_gets_only_notice`:
  where `allowPeer` refuses cid's peers, whatever this node's standing,
  no synced c, and of c only wire ops and owed notices go out. `MayGo`
  no longer needs this node live, so `removal_reaches_session` holds of
  every node.
- `link_owes_nothing`: nothing is owed to a link's peer.
- **`preadmit_sends_nothing`**, per step, and
  **`preadmit_reaches_session`**, over every entry point: on a session
  whose peers only the link lets in, no op of c goes out.
- `rooms_complete_take`: the joiner's session keeps c, taken.
- Negative control `shipped_roomFor_shows`: the shipped selection
  (`roomForShipped`) synced c with the link's peer, showing it every op.

## Evidence

tests/vacuity/IdentityPreadmit.lean (`vacuity_identity_preadmit`): Bob's
node, removed, holding Alice's community, opens Mallory's link over a
real Noise session. Its rooms view gives the session `[Room.take c]`;
the running steps and a whole `Node.onTick` send nothing of c; Mallory's
op of c is wanted and taken. The shipped selection on the same store
serves Bob's message. Then Dave, admitted after Bob's removal, invites
him back: that session takes c, takes Bob's new admission, and once
Dave's ops are held c is synced and Bob is live.

`mise run test:preadmit` (tests/engine/controls.txt): the witness, then
the mutants (tests/engine/preadmit_negative.py): `roomFor`'s link branch
syncing c is rejected inside `roomFor_law`; a take room answering from
the live index is rejected inside `Conn.view_items`.

## Not covered

- A take room's wants say which of the ids the peer offers this node
  lacks (no content).
- A node not live in c that opens a link naming a removed member's key
  still gives that member the notices of its removal, with their
  closures, as any node does (`refused_gets_only_notice` states it).
- That `dialOne`'s hello carries the join request is the code, run end
  to end by ProductionBootstrap, not a separate law.
