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
engine/
  core/        op, codec, ids, judging, store (SQLite and held), lists,
               the ephemeral log, react (responders run to a fixpoint)
  wire/        frames, couriers, the TCP runner, mDNS discovery
  renderer/    the component tree, layout, text, images, QR decoding,
               paint, and the API the platform shells implement
ops/
  sync/        hello, round, have, want: ephemeral ops and their
               responders; RBSR's answer and fingerprints; the Merkle
               cache
  connection/  the handshake and sessions (eph, request, connection,
               established, …)
  community/
    Community.lean   the family: the sum of its domains, laws across them
    membership/  message/  reaction/  profile/  name/  blob/  link/  …
  app/         ephemeral UI state: navigation, drafts, selection
App.lean       the root component
platforms/
  android/     the Android shell (activity, surface, IME, camera)
  ios/         the iOS shell (UIKit, IOSurface ring, camera)
  headless/    the scripted twin the tests drive
  quietd/      the daemon: no screen, the runner and a store
docs/
```

Each domain is two modules. `Message.lean` holds its fields, op types,
relations, intents and validator laws. `Message/View.lean` holds its
component, the component's laws and the end-to-end theorem. A daemon or
a cloud node imports every op module and no view.

## Where things are now

Step 2 moved every file of the five repositories' packages into this
tree with `git mv` (`git log --follow` follows each);
`ci/reorg-map.tsv` lists where each went. A module's name is its path
from the top (`engine/core/Codec.lean` is `engine.core.Codec`); the
namespaces inside are unchanged.

| in the tree | what is there now |
|---|---|
| `engine/core/` | lean-engine's `Engine/` (op, codec, judging, the SQLite store, lists, purge; `Engine.lean` imports all of the engine and sync), and from `Engine/Sync/`: `Sync.lean` (the intake), `Held.lean` (the held store) and `Locality.lean` (a verdict depends only on the op's requirement closure; core's purge laws are proven from it) |
| `engine/wire/` | lean-engine's `Engine/Sync/{Frame, Node, Tcp, Pair}`: frames, the node and its TCP runner; `mdns/`: lean-mdns |
| `engine/renderer/` | lean-quiet's `Quiet/{Data, Row, Text, Font, Paint, Image, Qoi, Emoji, Geometry, Sheet, SheetGeom, Platform, Camera, Arrival}` and the laws about them only (`TextLaws`, `WrapLaws`); `qr/` and `pic/`: lean-qr |
| `ops/sync/` | lean-engine's `Engine/Sync/{Fp, Round, RoundLaws, Wire, Conn, ConnLaws}`: rounds as functions, not yet ephemeral ops |
| `ops/connection/` | lean-engine's `Connection/` (`All.lean` imports all of it: `Connection.lean` is the connection op type); `bootstrap/`: lean-net's model, retired once its laws are re-proven over the two-node world |
| `ops/community/` | lean-engine's `Community/` as it was (`Facts.lean` not yet split by domain); lean-quiet's `Quiet/Kinds/*`, each its domain's view: `message/View.lean`, `profile/View.lean`, `reaction/View.lean`, `attachment/View.lean` (File), `membership/{Accepted,Request}View.lean`, and `link/View.lean` (the invite sheet, `Quiet/Link`); each view's laws beside it (`message/ViewLaws`, `reaction/RowLaws`, `attachment/ArrivalLaws`, `membership/RemovedLaws`) |
| `ops/app/` | lean-quiet's `Quiet/{Pages, Composer, Switch, Remove, PeopleLaws, Chaos}` (`Chaos` holds `Me`, the device's member in a community, besides the chaos generator) |
| `App.lean` | lean-quiet's `Quiet/App`; beside it `Main.lean`, the app over the platform seam (every shell's main), and `Quiet.lean`, which imports every module of the app |
| `platforms/android/`, `platforms/ios/` | lean-quiet's shells; `android/qr/`: lean-qr's camera harness |
| `platforms/headless/` | lean-quiet's `host/` twin and its programs (`QTests/`) |
| `platforms/quietd/` | not yet: lean-quiet's branch `daemon` |
| `tests/` | `Axioms.lean`, the one axiom audit (every part's laws), and `check.sh`, its gate; each part's suites, fixtures and negative controls in `tests/<part>/` |
| `docs/` | this file, `SYNC.md`, the parts' READMEs (`ENGINE.md`, `QR.md`, `MDNS.md`, `NET.md`) and `BUILD.md` |
| `tools/`, `third_party/`, `assets/` | lean-quiet's and lean-qr's tools; the vendored SQLite; the app's fetched data (not committed) |

lean-chat is not imported (archived as is).

Imports that still cross the rule, for step 3: `engine/core/Engine.lean`
imports `ops/sync`; `engine/wire/Node` imports `ops/sync/Conn`;
`engine/renderer/Data` (the app's live data) imports the Community and
Connection families; `ops/community/membership/RemovedLaws` imports
`App`.

## Steps

1. **Import.** At a pause point, rewrite each repo's history into its
   target directory (`git filter-repo`) and merge everything into one
   repository, so every commit and branch is kept.
2. **One build.** *Done (2026-10-28).* A single Lake package (each
   library pointed at its directory), one `mise.toml` with tasks per
   part, one CI. Module names are paths, so nothing collides (`Tests`
   is `tests.engine`, `tests.qr`, …).
3. **Refactors, by their owners, after the join demo:**
   - Community's `Facts.lean` split into domains;
   - the views (each domain's `View.lean`, once `Kinds/*`) turned into
     components that read only their own fact;
   - sync's rounds turned into ephemeral ops;
   - the ephemeral log added to the engine.
4. **Before the first push to the public repository,** scan every
   history for keys and tokens.
