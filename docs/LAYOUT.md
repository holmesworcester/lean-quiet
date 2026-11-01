# Layout

How Lean Quiet is split, and why. Approved by the user, 2026-10-27.

## The rule

Split by what a statement quantifies over.

- **The engine is everything that holds for every op type.** Its code
  and its laws take an op type's declaration as a parameter and never
  name a kind: wire decoding and op ids, judging, filing, lists, sync's
  rounds and fingerprints, subscriptions, the component tree, layout,
  paint. Each law there is proven once, for all kinds.
- **Ops are everything that names a kind.** The unit is a *domain*: a
  fact kind with the op types that produce it. Reactions are one
  register, written by react and unreact entries. Membership is
  invite, request, approve, admit and remove. A domain declares:
  - its fields;
  - its op types (body, validator, scope, claimed time);
  - its relations (the lists its fact is filed in);
  - its intents (how it is written);
  - its component (how its fact renders).

  The declaration carries proof obligations: an honest intent produces
  an op its validator accepts, keys and claimed time depend only on the
  op, and the component's pixels depend only on its fact.
- **End-to-end laws are compositions.** The engine proves one pipeline
  theorem, over any declaration that meets its obligations:

  > bytes → op → verdict → lists → live answer → component → pixels

  A domain's network-to-pixel theorem is its own obligations plus one
  application of that theorem, kept in the domain's folder.
- **A law that spans domains lives in the smallest module that imports
  everything it mentions.** "A message shows only if its author was
  admitted" lives with messages, which cite admissions. "A removed
  member is cut off" lives at the family's root.

## State is ops

The only state that is not ops:

1. **The sockets at the seam.** Bytes come in and go out by address.
   An inbound frame's ops are taken through an intake; outbound bytes
   are couriers, as in poc-17.
2. **Caches derived from ops,** each with a law "cache = f(ops)": the
   list index, the in-memory room index, and later the Merkle tree.

Everything else is an op.

- **Durable ops** are stored in SQLite: shared ones are synced in their
  room, local ones never leave the device.
- **Ephemeral ops** live in an in-memory log: never stored, never sent,
  read with the same lists as everything else. They hold:
  - the app's own state: navigation, drafts, selection, open sheets;
  - sync's rounds and messages (hello, claims, have, want);
  - a session's liveness.

  Only a scroll's per-frame physics stays in the renderer; where it
  comes to rest is an op.

- **Components read only their own fact** (a list of one, by id). A
  component names its children as (kind, id) or as a list (relation,
  key, window). The renderer unfolds the tree, and re-reads a component
  only when its key fires (`eval_stable`).
- **A screen is a component.** The app is one root component.

## Tree

```
engine/          what holds for every op type; it imports nothing under app/
  core/          op, codec, ids, judging, store (SQLite and held), lists,
                 the ephemeral log, react; the Merkle tree; FIFO fairness
  wire/          frames, couriers, the node and its TCP runner, Noise, mDNS
  sync/          hello, round, have, want; RBSR's answer and fingerprints
  renderer/      the component tree, layout, text, images, QR decoding,
                 paint, and the API the platform shells implement
app/             the op tree: one folder per op, nested by what it cites
  Commands.lean  the node's hooks over both families; the app's live data
  Screen.lean    the root component: the app
  Proofs.lean    laws over the node and the whole app
  community/     the root op (Op, Validate), its family (Family) and the
                 laws, intents and screens across its ops; under it name/,
                 profile/, key/wrap/, device/{secret,endpoint}/,
                 member/{invite/request/approve/admit, admin, remove,
                 join/{joining/abandon, accept}}/,
                 channel/message/{reaction, receipt, attachment/chunk, draft}/
  connection/    the handshake and sessions: eph, request, opened,
                 connection, established, send, recv, given (its Family
                 is over the community's facts too)
platforms/
  android/  ios/  macos/  windows/  linux/  desktop/
  headless/      the scripted twin the tests drive
tests/           the axiom audit, the wiring audit, each part's suites
docs/
```

**Eight file names.** Nothing else lives under `app/` (`ci/layout.py`):

| File | What it holds |
|---|---|
| `Op.lean` | the op: its body, its fact, their codecs, the relations its fact is filed in, scope and claimed time |
| `Validate.lean` | its validator: the facts it cites, typed, and the fact it produces |
| `View.lean` | the component for the op's fact, and its laws |
| `Commands.lean` | intents and responders over the ops in this folder and below |
| `Screen.lean` | components that compose several ops, and their laws |
| `Proofs.lean` | laws over the ops in this folder and below |
| `Tests.lean` | tests of the ops in this folder (planned: today in `tests/`) |
| `Family.lean` | the registry: the family's closed sum of its ops, the dispatch of codecs and validators to each op type, and what its laws and intents stand on |

**Placement by what a declaration names.** A law, command or screen
lives in the deepest folder that holds every op it names; a folder sees
its own subtree and its ancestors, a validator the `Op.lean` of each op
it cites. Siblings meet at their common ancestor: `message_authorized`
(a message and its author's admission) is in `channel/message/`,
`removal_cuts_off` at `community/`, the node's room laws at the root.
A daemon or a cloud node imports `app/Commands.lean` and no screen.

## Where things are now

Step 2 moved every file of the five repositories' packages into the
tree with `git mv`; `ci/reorg-map.tsv` lists where each went. The op
tree's cutover (2026-10-31) split and merged them into one folder per op;
`ci/optree-map.tsv` lists, for each file it removed, the files its
declarations are in now. A module's name is its path from the top
(`app/community/member/remove/Proofs.lean` is
`app.community.member.remove.Proofs`); the namespaces inside are
unchanged, except the Merkle tree's (`Merkle`, was `Community.Merkle`).

- `app/community/Proofs.lean` imports the whole community subtree, and
  `app/connection/Proofs.lean` the connection one: what imported a
  family's umbrella imports these.
- The bootstrap model (lean-net's) names only community ops: it is a
  section of `app/community/Proofs.lean`, retired once its laws are
  re-proven over the two-node world.
- The app's live data (the store on SQLite, its writer, live answers,
  the outbox) names the node's family: it is in `app/Commands.lean`.
- `Main.lean` runs the app on a platform; `Quiet.lean` imports every
  module of the app.

No engine module imports `app/`, and every import under `app/` goes down
the tree, up to an ancestor, or to a cited op's `Op.lean`; across the
families, only connection to community (`ci/layout.py`).

## Steps

1. **Import.** At a pause point, rewrite each repo's history into its
   target directory (`git filter-repo`) and merge everything into one
   repository, so every commit and branch is kept.
2. **One build.** *Done (2026-10-28).* A single Lake package (each
   library pointed at its directory), one `mise.toml` with tasks per
   part, one CI. Module names are paths, so nothing collides (`Tests`
   is `tests.engine`, `tests.qr`, …).
3. **Refactors, by their owners, after the join demo:**
   - Community's `Facts.lean` split into domains (*done: each op's
     `Op.lean` and `Validate.lean`*);
   - the views (each domain's `View.lean`, once `Kinds/*`) turned into
     components that read only their own fact;
   - sync's rounds turned into ephemeral ops;
   - the ephemeral log added to the engine.
   - one folder per op: *done (2026-10-31)*, the [op tree](OP_TREE.txt),
     drawn in the workspace (`mise run workspace:serve`), with the rules
     in [OP_WORKSPACE_REQUIREMENTS.md](OP_WORKSPACE_REQUIREMENTS.md)
     (LAYOUT01–06) and `ci/layout.py` enforcing them.
4. **Before the first push to the public repository,** scan every
   history for keys and tokens.
