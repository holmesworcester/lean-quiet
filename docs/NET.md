# lean-net

How two Quiet nodes in Lean get connected: the protocol rules as
functions (`Net/Node.lean`), and proofs that bootstrap from an invite
link is possible over an ideal socket and inevitable over a failing one,
without ever connecting anyone who has not been approved. It builds on
lean-engine's `net-admission` branch (requests, approvals, admissions)
and judges the real ops with the real validators.

## The protocol

After poc-17's op-as-wire model over TCP (a hello sealed to the dialed
key, an answer proving the responder holds it, then sync over the
session) and libquiet's request/vouch/admission:

- **A request is an op.** The joiner composes it once, when it pastes the
  link. It is signed by the link's bearer key and by the joining device,
  and it admits nobody. Members approve it with signed approval ops that
  cite it. An unsigned admit op tallies exactly the invitation's
  threshold of approvals, by distinct users, into the admission
  (lean-engine `Community`).
- **Delivered, not connected.** The joiner's hello carries the request.
  The inviter stores it if it is a Valid request (the only op it reads
  from a peer it does not trust) and answers only if it now trusts the
  sender. A request alone opens nothing and earns no reply. The joiner
  re-sends the same hello every tick, until approval lets the answer
  through.
- **One trust rule at both ends.** A node opens a session for c with
  device p if p is a live member by its own ops (`allowPeer`). Before the
  node itself is admitted, it may also open one with the device its link
  names, as long as its ops say nothing about that device yet. The
  responder applies this to the initiator, and the initiator to the
  responder. `allowPeer` has no exception: the link clause belongs to
  the joiner, and ends at its admission.
- **Bootstrap facts are local.** Accepting a community, the pending link
  and the sessions are all node-local, never ops. The wire cannot create
  them. Ops of other communities are dropped.

## The laws

The scene (`Net/Scene.lean`) is this one. Founder A creates c and
invites B with a member invitation needing one approval. B pastes the
link. A's user approves when it chooses. The ops are composed by
lean-engine's own `Compose` (SHA-256 ids, Ed25519 signatures).

| law | statement |
|---|---|
| `no_connection_before_approval` | In every state reachable over a socket that drops, duplicates and reorders, until A holds B's admission: neither side has a session, no answer and no A ops are in flight to B, and B holds only its request. |
| `sessions_trusted` | Every session A holds is with a device A's ops admit, with no exception. Every session B holds is with a device B trusts by the rule. |
| `bootstrap_possible` | An explicit lossless run of nine enabled steps, each named, ends bootstrapped. |
| `bootstrap` | In every fair run over a failing socket, eventually and from then on: both sessions are open, both nodes hold the same ops, each admits the other by its own ops alone, and B has forgotten its link. |
| `bootstrap_ideal` | The same for fair runs with no loss. |
| `allowPeer_iff`, `allowPeer_settles` | The model's `Allowed` is what the engine's `allowPeer` view (lists over the persisted tables) answers once its queue is empty, which it always reaches. |
| `admitted_inv`, `allowedA`, `allowedB` | Among the scene's ops, A is admitted exactly when the root is held, and B exactly when its admission is. Nobody is removed. |

"Fair" means three things. Both nodes tick forever. A's user eventually
approves. The socket is fair-lossy: a message sent at infinitely many
steps is delivered at infinitely many. Any message may still be lost any
finite number of times. Bootstrapped means `Scene.Goal`.

## What is assumed (`Scene.Good`)

- The signature scheme verifies what the three key pairs sign.
- A and B are different devices.
- The five ops' ids are distinct, so SHA-256 does not collide on them.

`tests` checks all three for real keys.

## What is abstracted, and not proven here

- The handshake's cryptography. A hello is read only by its addressee,
  and an answer is taken only from the device that was dialed. Secrecy
  and authentication against an active attacker are not modeled. The
  socket fails; it does not lie.
- Sync, modeled as "push the community's ops over the session".
  Fingerprint reconciliation is its own protocol.
- The node functions decide on Props, through `Classical`. The running
  code is to call `allowPeer`, which `Net.Bridge` proves gives the same
  answers at rest.
- The scene is two nodes, one invitation with threshold 1, and a founder
  who invites and approves. These are not exercised here:
  - k-of-n approvals across members (lean-engine proves those);
  - members redialing members;
  - removal of the inviter mid-bootstrap (the `¬ Known` clause);
  - answers from strangers.

## Tests

`mise run check` runs `tests/check.sh`:

- It builds every proof.
- It checks that the 11 laws rest on `propext`, `Classical.choice` and
  `Quot.sound` only.
- It refuses `sorry`, `axiom`, `native_decide` and externs in the model.
- It runs `scene_check`: every subset of the five ops, in two orders,
  received into SQLite with real Ed25519. The running `allowPeer` and
  verdicts (read as lists under each op's own key), and the dial set, must
  match the scene's table.
- It runs the negative controls. Each one changes a rule so that a law
  becomes false, and the build must refuse it:
  - an inviter that answers without trusting the sender;
  - no link clause;
  - a shut bare door;
  - no hello retry.
