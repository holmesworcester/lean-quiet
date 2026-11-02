# Rules for agents working in this repository

## Proofs are about running code, never about models

A law (a theorem `tests/Axioms.lean` audits) must be about the code that
runs: every definition its statement names, premises included, is
reached from the app's `main` or the node's runner. A model (a parallel
definition, a copy of a function, an abstract machine, code nothing
calls) is allowed only with a `bridge` in `tests/wiring.txt`: an audited
equation or iff that proves the model equal to running code.

- Port a model law by restating it over the function the app calls
  (factor the running code if needed, so the function it calls is the
  one the law is about), or by proving its model equal to that code.
  Delete it if a law about running code already says as much.
- Never weaken a statement to make it fit. A law that cannot hold of the
  running code is a finding: a gap, or a bug the model hid (add bugs to
  `docs/CAUGHT.md`).

The wiring check enforces this (`tests/Wiring.lean`, run by
`ci/proof-links.py --check`, the `readme` gate of `ci/local.sh`). It
classes every law as wired, World, control, step or model, and fails on a
model law that `tests/wiring-models.txt` does not list. A step is a lemma
that would be a model, but that a law about running code uses in its
proof; the check finds the use, and a README row that cites a step must
cite that law too. A structure or inductive the running code never names
(a `World` record, a `Run` of steps) counts as part of the statement: what
its fields name must run too, so a harness step hidden in a `Run`'s
`next` field makes the law a model. `tests/wiring-models.txt` holds the model laws there
were when the rule was made (2026-11-01). It only shrinks: the check fails while it names a law that is no longer a model
(delete the line: `ci/proof-links.py --prune`), and on a line the merge
base with origin/main did not have. Never add a line to it.

World laws (the running node's code over a modelled network) are counted
apart; bring them onto the app's own transport, too.
