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

## From today's repos

| today | goes to |
|---|---|
| lean-engine `Engine/` (core) | `engine/core/` |
| lean-engine `Engine/Sync/` (rounds, Conn, Node) | `ops/sync/` (rounds as ops) and `engine/wire/` (frames, runner) |
| lean-engine `Community/` | `ops/community/`, split by domain |
| lean-engine branch `connection`: `Connection/` | `ops/connection/` |
| lean-quiet `Quiet/{Data, Row, Text, Font, Paint, Image, Qoi, Emoji, Geometry, Sheet*, Platform}` | `engine/renderer/` |
| lean-quiet `Quiet/Kinds/*` | each domain's `View.lean` |
| lean-quiet `Quiet/{App, Pages, Composer}` | `App.lean` and `ops/app/` |
| lean-quiet `android/`, `ios/`, `host/` | `platforms/android/`, `platforms/ios/`, `platforms/headless/` |
| lean-quiet branch `daemon` (lean-quiet-daemon) | `platforms/quietd/` |
| lean-mdns | `engine/wire/mdns/` |
| lean-qr | `engine/renderer/qr/` |
| lean-net | retired once its laws are re-proven over the two-node world (`ops/connection/`) |
| lean-chat | not imported (archived as is) |

## Steps

1. **Import.** At a pause point, rewrite each repo's history into its
   target directory (`git filter-repo`) and merge everything into one
   repository, so every commit and branch is kept.
2. **One build.** A single Lake package (each library pointed at its
   directory), one `mise.toml` with tasks per part, one CI. Module-name
   collisions (`Tests`, `Main`) get renamed.
3. **Refactors, by their owners, after the join demo:**
   - Community's `Facts.lean` split into domains;
   - `Kinds/*` turned into components that read only their own fact;
   - sync's rounds turned into ephemeral ops;
   - the ephemeral log added to the engine.
4. **Before the first push to the public repository,** scan every
   history for keys and tokens.
