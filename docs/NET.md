# lean-net (retired)

This file described the bootstrap **model**: a noncomputable two-node
protocol (`Net.step`, `Net.recv`, `Net.onHello`, …, with `Scene.Good`
and `Run.Fair`) and its laws (`no_connection_before_approval`,
`sessions_trusted`, `bootstrap`, `FairExecution`). Nothing that runs
imported it, so its laws were about a protocol the app does not run. It
was deleted on 2026-11-01 (proofslop forensics, finding 4; the standing
rule that a model without a refinement theorem is not evidence).

What stands in its place, over the code that runs:

- **No session before approval.** The responder answers, or re-answers,
  only a peer the trust rule takes (`answer_trusted`, `resend_trusted`),
  and the trust rule takes exactly the live members' nodes
  (`connect_iff`). Not yet: the same guarantee as an invariant over every
  entry point of the running node.
- **A joiner connects.** `Connection.Execution` runs the actual
  `Node.onTick`/`onFrame`/`onWrite`/`onClose` with the production hooks,
  native crypto and an explicit store; a native-certified successful
  prefix has a fair continuation (`successful_fair_extension`). Not yet:
  convergence for every fair execution of the running app (the target
  theorem: docs/BOOTSTRAP-LIVENESS.md).
- **The scene on the real engine.** `tests/net/SceneCheck.lean` composes
  the five ops of a join (root, invitation, request, approval,
  admission) with the functions the app runs, receives every subset in
  shuffled orders into SQLite, and checks the running `allowPeer`,
  `members` and verdicts. `tests/net/negative_controls.sh` mutates the
  running trust rule, the admission validator and the responder's trust
  check; the proofs must refuse each.
- **Before admission, nothing of c goes out.** A session the link
  clause alone lets in (the joiner's, with the inviter its pending join
  names) carries the community taken, not synced: the joiner learns of
  its admission and sends none of it; its request went in the hello
  (`preadmit_sends_nothing`, docs/TAKE-ROOM.md).
