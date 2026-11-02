# Headline laws: a proposal

**Status: approved by the user (2026-11-01).** No law's statement was
changed. An agent drafted this list on 2026-11-01 for the Vibecheck
judges' questions ([rules](VIBECHECK-RULES.md)): are the laws
important, are they about the code itself, and do they pass Comparator?

**Second pass (2026-11-01).** The user dropped `Op.id_decode` and
`Remove.writes_only_after_two` from the top list, and asked for strong
laws about the screen and about cost. Five such laws are now in the top
list (12, 13, 15, 16, 17), beside `back_open` (14). `wrap_keeps` moved
to "Also considered": the new screen laws promise more.

**Third pass (2026-11-01).** The user approved the seventeen, and
`deviceCut_removal` as the eighteenth once it had a concrete example
(it has one now, in tests/vacuity/IdentityPeople.lean). The user also
approved moving the definitions that kept seven laws from being judged
under their own names; that is done, and all eighteen pass Comparator
both ways (see [Comparator](#comparator)).

The app has about 1,400 audited laws. This page picks eighteen that a
judge should read first. For each one it gives:

- the law in plain words;
- its Lean name and place;
- its **class**, from tests/Wiring.lean: *wired* means the law is about
  code that runs in the app;
- its **spec surface**: the definitions that the statement depends on
  (CLAUDE.md, section 4), and the part of them that a reviewer must read;
- its **axioms**;
- an **example**: a concrete input that meets every hypothesis
  (tests/vacuity);
- a **control**: a bad output that the law or its check rejects, a
  mutant that breaks the law, or a bug that the law caught.

To check every number on this page, run `mise run test:headline`
(tests/headline.sh). It builds the tree, runs tests/Headline.lean,
checks that this page's generated section is current
(ci/headline.py), and checks the Comparator files.

## How to read a surface

`#headline` (tests/SpecSurface.lean) walks from a law's statement
through the bodies of the definitions it names. It counts only this
repository's definitions. It then sorts them:

- **Of the app:** code that runs in the app (`main`, the node's runner
  or a platform entry point reaches it), and the types that code uses.
  This is what the law is *about*. A reviewer does not need to read it
  to know what the law says, but the law covers it.
- **Spec-only:** predicates and other definitions that exist only to
  state laws. **A reviewer must read these.** A wrong one makes the law
  say something else.
- **Assumed:** an assumption that tests/wiring.txt names: the store
  model that stands for SQLite (`Model.run`), Ed25519 unforgeability
  (`Unforgeable`), no hash collision (`Distinct`), the symbolic model of
  the cryptography (`sym`). Each is read once, in the README's
  [What is Assumed](../README.md#what-is-assumed). The walk stops at it.
- **Bridged:** proven equal to running code by a law. A copy of running
  code (`stepS` is the engine's `step` on the store model, by
  `run_step`), or the cost meter (`CostT`), which audited equations
  erase to the plain run (`erase_bind` and the others). The walk stops
  at it.

"Surface" in the tables is the whole walk, as CLAUDE.md's
`#spec_surface` defines it. "Review" is the spec-only part plus the
assumptions.

## The eighteen, ranked

| # | The law, in plain words | Lean name | Class | Review | Example | Control |
|---|---|---|---|---|---|---|
| 1 | Nobody can post as another user. | [`no_impersonation`](../app/community/Proofs.lean#L121) | wired | 6 + `Unforgeable` | conditional | forged post rejected |
| 2 | Nobody joins without a member's approval. | [`admission_needs_approval`](../app/community/member/invite/Proofs.lean#L44) | wired | 8 | runtime | 4 bad joins rejected |
| 3 | Only admins remove other members. | [`removal_authorized`](../app/community/member/Proofs.lean#L51) | wired | 8 | runtime | unauthorized removal rejected |
| 4 | A removal cannot be undone. | [`removed_stays`](../app/community/member/remove/Proofs.lean#L10) | wired | 7 | runtime | none |
| 5 | The node connects only to live members. | [`connect_iff`](../app/community/Proofs.lean#L823) | wired | 10 + store model | runtime | refused after removal |
| 6 | After a removal, the removed member gets only the notice. | [`removal_reaches_session`](../app/Proofs.lean#L3012) | wired | 13 + store model | runtime | message withheld |
| 7 | A session sends only what its peer may see. | [`recv_send`](../engine/sync/ConnLaws.lean#L185) | wired | 3 + store model | kernel | none yet |
| 8 | The node checks a frame before it reads it. | [`sealed_auth`](../app/connection/Proofs.lean#L160) | wired | 2 + store model | runtime | 3 damaged frames rejected |
| 9 | Session keys stay secret. | [`kk_secret`](../engine/wire/NoiseSymbolic.lean#L510) | wired, symbolic | 7 + `sym` | kernel | tight: a leak breaks it |
| 10 | The dialer knows who answered. | [`kk_authentic`](../engine/wire/NoiseSymbolic.lean#L801) | wired, symbolic | 8 + `sym` | kernel | mutant `read1Slip` |
| 11 | Devices that hold the same ops agree. | [`same_ops_same_verdicts`](../engine/core/Termination.lean#L122) | wired, bridged | 2 + `Distinct` | runtime | reversed order, replay |
| 12 | Every phone shows a channel's messages in the same order. | [`display_agrees`](../app/community/channel/message/Proofs.lean#L198) | wired | 8 | runtime | reversed arrival order |
| 13 | Scrolling never shows a blank. | [`Cover.covered`](../engine/renderer/Cover.lean#L53) | wired | 0 | kernel | blanks exist outside it |
| 14 | Back goes back. | [`back_open`](../app/Proofs.lean#L1320) | wired | 1 | runtime | shipped bug, a mutant |
| 15 | Tapping a community opens that community, even when two share a name. | [`select_tapped_dedupe`](../app/community/Screen.lean#L812) | wired | 0 | kernel | pinned iPhone bug |
| 16 | Letting someone in costs at most three ops, however big the community. | [`approveReq_ops`](../app/community/Proofs.lean#L1329) | wired | 2 | no premises | mutant `approveWrapAll` |
| 17 | Storing an arriving op costs a fixed number of store operations, however big the community. | [`ingest_costs`](../engine/core/IngestCost.lean#L49) | wired, metered | 6 | no premises | none yet |
| 18 | The app says "You've been removed" only when the store holds a removal of you. | [`deviceCut_removal`](../app/community/Screen.lean#L606) | wired | 2 + store model | runtime | mutant from a real bug |

"Review" counts the spec-only definitions, then names the assumptions;
the counts come from the generated section at the end of this page.
"kernel" means Lean's kernel checks the example; "runtime" means the
example runs native code (real Ed25519, SQLite, rendering) and then
applies the law, so it trusts Lean's compiler too; "conditional" means
one hypothesis stays an assumption; "no premises" means the law has no
hypothesis to meet. All eighteen use only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

The order puts first what a user is promised about other people
(1–6), then what leaves the device (7–8), then the sessions (9–10),
then agreement (11–12), then the screen (13–15), then cost (16–17),
then what the app tells the user about a removal (18).
Among the screen and cost laws, the order is by how much the law
promises and how easily a person who does not program sees it in a
demo.

### 1. Nobody can post as another user

If the store holds no forged signature, the holder of device d's key
signed each valid message from d, as that exact op. The same key holder
also signed the op that put d into its user.

- **Rests on** `Unforgeable`: Ed25519's unforgeability, stated over the
  signatures that one store holds. It is a computational assumption that
  Lean cannot prove. `unscoped_signs_all`
  ([app/community/Proofs.lean:94](../app/community/Proofs.lean#L94))
  shows why it is scoped to one store: the unscoped form says nothing.
- **Example:** conditional. `Vacuity.Identity.noImpersonation`
  ([tests/vacuity/Identity.lean:74](../tests/vacuity/Identity.lean#L74))
  checks a real signed message by the running validator. The kernel
  example `unforgeableScoped`
  ([tests/vacuity/Contracts.lean:125](../tests/vacuity/Contracts.lean#L125))
  shows that `Unforgeable` can hold with an informative `Signed`.
- **Control:** the running validator judges a post by Mallory that
  claims to be Bob's Invalid (tests/vacuity/Identity.lean, `forged post`).
- **Note:** laws 1–4 are about `V`, the verdict of the spec (`Spec`,
  the least fixed point of the app's own `judge`). `status_iff_spec`
  ([engine/core/Proofs.lean:484](../engine/core/Proofs.lean#L484)) proves
  that, once judging settles, the store holds exactly that verdict.

### 2. Nobody joins without a member's approval

Each admitted device is the founder's, or its admission cites a valid
join request for that device and one valid approval of it. A different
admitted device signed the approval. For a new device of an existing
user, the approver is that user. A valid request needs the invitation's
signature (`request_invited`).

- **Example:** runtime. `Vacuity.Identity.admissionNeedsApproval`
  ([tests/vacuity/Identity.lean:79](../tests/vacuity/Identity.lean#L79)):
  Alice approves Bob, with real Ed25519 signatures.
- **Control:** the running validator rejects a missing approval, a self
  approval, duplicate approvals, and a wrong invitation signature.

### 3. Only admins remove other members

A valid removal of user t by user u is a self-removal, or u is an admin.

- **Example:** runtime. `Vacuity.Identity.removalAuthorized`
  ([tests/vacuity/Identity.lean:86](../tests/vacuity/Identity.lean#L86)).
- **Control:** Bob's removal of Alice that cites his admission, not an
  admin grant, is judged Invalid.

### 4. A removal cannot be undone

When more ops arrive, in any order or after any delay, a removed user
stays removed.

- **Example:** runtime. `Vacuity.Identity.removedStays`
  ([tests/vacuity/Identity.lean:122](../tests/vacuity/Identity.lean#L122)).
- **Control:** none. The law says that a fact stays true; there is no
  bad output to reject.
- **Note:** this is about the removed *user's* ops. A removed member can
  still invite and approve a new device on its own node (see
  [claims that need care](#readme-headline-claims-that-need-care)).

### 5. The node connects only to live members

When judging is complete, the trust rule (`allowPeer`, read from the
node's tables) accepts a node key if and only if a live device is
admitted under that key. A device is live if it is admitted and none of
its users is removed.

- **Rests on** the store model (`Engine.DB`, `View.eval`).
- **Example:** runtime. `Vacuity.IdentityTrust.connectIff`
  ([tests/vacuity/IdentityTrust.lean:41](../tests/vacuity/IdentityTrust.lean#L41)).
- **Control:** the same fixture accepts Bob before his removal and
  refuses him after it.

### 6. After a removal, the removed member gets only the notice

Whatever the node runs (a frame, the clock, a write, a socket that
closes), every frame it sends on a session carries, of each community
where this node is live and the trust rule refuses the peer, only sync
messages and the removal with the ops that the removal needs.

- **Rests on** the store model, and on hypotheses that the node's
  hooks, catalog and retry store only read.
- **Example:** runtime. `Vacuity.IdentityLifecycle.removalReachesSession`
  ([tests/vacuity/IdentityLifecycle.lean:203](../tests/vacuity/IdentityLifecycle.lean#L203))
  runs a whole `onTick` of Alice's node over a real Noise session with
  removed Bob.
- **Control:** the frame for Bob, opened with the real session key,
  carries the removal and not Bob's message.
- **Note:** its surface is the largest of the eighteen. See
  [surfaces too big](#surfaces-too-big-to-review).

### 7. A session sends only what its peer may see

A connection replies only with sync messages and with ops of the rooms
that the connection is let into. A local op, such as a session key or a
pending join, is in no room, so it is never sent. (`rooms_trusted`
proves that the connection's rooms are the ones the trust rule allows.)

- **Rests on** the store model.
- **Example:** kernel. `Vacuity.Network.receiveSendable`
  ([tests/vacuity/Network.lean:107](../tests/vacuity/Network.lean#L107)).
- **Control:** none yet. A good one: a want for a local op or for an op
  of another room gets no reply.

### 8. The node checks a frame before it reads it

If a sealed frame fails its AEAD check under the receive key of the
session that it names, the node and its store do not change, and the
node sends nothing. No part of the frame is decoded first.

- **Rests on** the store model.
- **Example:** runtime. `Vacuity.IdentityFrames.sealedAuth`
  ([tests/vacuity/IdentityFrames.lean:122](../tests/vacuity/IdentityFrames.lean#L122)),
  over a real Noise session and XChaCha20-Poly1305 frame.
- **Control:** a frame with one byte changed, a frame under the wrong
  key, and a frame with a changed header are all rejected and change
  nothing.

### 9. Session keys stay secret

An active attacker that does not know a session's four secrets (both
static keys and both ephemeral keys) cannot get either side's session
keys, whatever calls it makes to honest nodes. The law is about the
handshake functions that run (`sent1`, `read1`, `read2`, `write2`),
with the cryptography as symbols (Dolev-Yao).

- **Rests on** the symbolic model (`sym`): perfect primitives, no
  computational proof.
- **Example:** kernel. `Vacuity.Session.secretsHeld`
  ([tests/vacuity/Session.lean:42](../tests/vacuity/Session.lean#L42)).
- **Control:** `kk_secret_init_tight`
  ([engine/wire/NoiseSymbolic.lean:531](../engine/wire/NoiseSymbolic.lean#L531)):
  an attacker that knows the initiator's static and ephemeral keys does
  get the keys. So the hypothesis is needed, and the attacker model is
  strong enough to break a weak handshake.

### 10. The dialer knows who answered

Unless the dialed node really answered this request, the dialing node
accepts no reply that an attacker can make. The dialed node's static
key must be secret, and the dialer's static or ephemeral key.

- **Rests on** the symbolic model (`sym`).
- **Example:** kernel. `Vacuity.Session.initiatorAuthenticates`
  ([tests/vacuity/Session.lean:125](../tests/vacuity/Session.lean#L125)).
- **Control:** `read1Slip`, a one-letter slip in the responder's code,
  lets the attacker forge a request (`read1Slip_forged`,
  [engine/wire/NoiseSymbolic.lean:976](../engine/wire/NoiseSymbolic.lean#L976),
  a negative control in tests/wiring.txt). `kk_authentic_tight`: with
  the responder's static key leaked, the attacker forges a reply.
- **Not covered:** replay. An old answer can be accepted again.

### 11. Devices that hold the same ops agree

Two nodes that received the same ops, in any order and in any batches,
with judging in between, both finish judging. They then hold the same
verdict for every op.

- **Rests on** `Distinct` (no two received ops share an id: no SHA-256
  collision among them) and the store model. The law names `drainS`,
  the engine's own `drain` on the store model (bridged by `run_drain`,
  `run_step`, `run_ingest`, `run_purge`).
- **Example:** runtime. `Vacuity.CoreRuntime.eventuallyAgree`
  ([tests/vacuity/CoreRuntime.lean:55](../tests/vacuity/CoreRuntime.lean#L55)),
  over a real signed community.
- **Control:** the fixture feeds the ops in reverse order and replays
  some.

### 12. Every phone shows a channel's messages in the same order

Two devices that hold the same two messages of a channel list them in
the same order. The one exception: both messages claim a counter of
2^63 or more, which only a hostile sender does; then each device shows
its own arrival order, and that rule is a law too (`arrival_order`).

- **Demo:** two phones side by side, messages sent from both, and from
  a third that was offline. Both phones show one order.
- **Example:** runtime. `Vacuity.RendererSupplement.displayAgreement`
  ([tests/vacuity/RendererSupplement.lean:139](../tests/vacuity/RendererSupplement.lean#L139)),
  with real Ed25519 messages stored in reverse order.
- **Control:** the fixture reverses the order in which the messages are
  stored, and drives a saturated counter. No mutant yet; a sort by
  arrival time would be a good one.
- **Note:** `order_total` adds that the list has no ties.

### 13. Scrolling never shows a blank

Every position in the conversation's content, from the bottom padding
up to the last loaded row, and above it while older messages are still
to load, shows a line of a message or a placeholder. The law is about
`Cover.seen`, the function that the running frame paints by. Its whole
surface is three definitions, all the app's own.

- **Demo:** fling the conversation up and down, keyboard open or not.
  No blank band appears.
- **Example:** kernel. `Vacuity.RendererGeometry.coverage`
  ([tests/vacuity/RendererGeometry.lean:102](../tests/vacuity/RendererGeometry.lean#L102)).
- **Control:** kernel examples in the same file show that `Cover.seen`
  does return a blank outside the content (below the padding, and past
  the last row when nothing more is to load), so the law excludes a
  blank that the code can make.
- **Not covered** (the README row is 🟡): that each frame arrives in
  time. Frame work is not bounded yet, and the OS's scheduling and the
  compositor are outside the proofs. The shift of the drawn buffer at
  each vsync is `Translate.covered` (also considered).

### 14. Back goes back

After the user opens a page, Back restores the app state from before,
except for a few fields that belong to the page that closed (its
one-line field, its refusal, its key, its scroll mark, its own sends,
what it presents) and an editor counter.

- **Example:** runtime. `Vacuity.RendererRuntime.backOpen`
  ([tests/vacuity/RendererRuntime.lean:17](../tests/vacuity/RendererRuntime.lean#L17))
  starts a real headless app.
- **Control:** `shipped_back_open_fails`
  ([app/Proofs.lean:1420](../app/Proofs.lean#L1420)). This law caught a
  shipped bug: commit 566e566 lost the switcher's backdrop after gear →
  back. The shipped code is kept as a mutant, and the kernel proves that
  it breaks the law ([what the proofs caught](CAUGHT.md)).
- **Note:** its whole surface is large (224) only because the app's
  state has about 150 fields. The spec-only part is one predicate.
### 15. Tapping a community opens that community, even when two share a name

In the community switcher, selecting the entry at row i, by its
account, gives back exactly that entry. No two entries share an
account or a community (`dedupe_nodup`, `dedupe_one_per_community`).
Its whole surface is nine definitions, all the app's own.

- **Demo:** join two communities with the same name, and tap each.
- **Example:** kernel. `Vacuity.RendererSets.tapped`
  ([tests/vacuity/RendererSets.lean:35](../tests/vacuity/RendererSets.lean#L35)),
  with entries of the same name and community.
- **Bug:** seen on an iPhone. A tapped row was matched back to its entry
  by short id and name, so twins always opened the first. The fix
  (03d33a9) carries each row's index; this law and `switcherOrder_sound`
  and `switcherOrder_complete` pin it ([what the proofs caught](CAUGHT.md),
  "found otherwise"). The shipped code is not kept as a mutant.

### 16. Letting someone in costs at most three ops, however big the community

Approving a join request writes at most three ops: the approval, the
admission, and one wrap of the content key, to the new member's node.
This holds whatever the store answers (`Always`), so it holds in a
community of any size. It also means the content key goes to the new
member only.

- **Demo:** approve someone in a small community and in a large one;
  each approval writes the same three ops.
- **Example:** no premises to meet.
- **Control:** `approveWrapAll`, an approval that wraps the key to every
  member, is a mutant in tests/wiring.txt. `wrapAll_over`
  ([app/community/Proofs.lean:1431](../app/community/Proofs.lean#L1431))
  proves that it writes four ops in a community of three, so it breaks
  the law.

### 17. Storing an arriving op costs a fixed number of store operations

Taking in an op costs one read, at most two writes and three index
lookups of the store, whatever the store holds. The count is made by
the cost meter (`CostT`), which audited equations erase to the running
code, on any store the code runs on.

- **Example:** no premises to meet.
- **Control:** none yet for this law. (The cost laws of the codec, the
  Merkle tree and pictures have mutants over their budgets.)
- **Not covered:** an index lookup is a B-tree descent in SQLite, which
  grows as the logarithm of the store's size; that is SQLite's file
  format, assumed (docs/PERF.md). And *judging* the op afterwards
  (`step_costs`) costs work in its requirements and in the ops that
  waited on it, which nothing caps yet (docs/PERF.md, "Every step that
  grows with N"). So the promise is about storing, not about the whole
  of receiving.

### 18. The app says "You've been removed" only when the store holds a removal of you

When the app marks this device cut from a community (`deviceCut`, which
`Accepted.read` uses to tell the member "You've been removed"), the
store holds one of the device's admissions into the community and a
removal of that admission's user. An admission not yet read, or a stale
read of one, never makes the mark.

- **Demo:** remove a member; only then does that member's phone say so.
- **Example:** runtime. `Vacuity.IdentityPeople.deviceCutRemoval`
  ([tests/vacuity/IdentityPeople.lean](../tests/vacuity/IdentityPeople.lean)):
  after Alice removes Bob, in a real signed community, the running
  `deviceCut` marks Bob's device, and the law applies. The same fixture
  checks that Bob's device is not marked before his removal.
- **Bug:** the gate's pixel test found members told "You've been
  removed" when no one had removed them: the shipped mark used two reads
  that need not agree. The shipped code is kept as a mutant
  (`removedShipped`), and `shipped_removed_without_removal` proves that
  it marks a member removed with no removal read
  ([what the proofs caught](CAUGHT.md)).
- **Not covered:** the law is about what the store's lists hold. That
  they list only valid ops is the engine's invariant (`Inv`), not a
  premise here; laws 3 and 4 say which removals are valid.

## What the eighteen rest on, together

To trust all eighteen, a reviewer reads **50 spec-only definitions**
(38 of them predicates) and **4 assumptions**:

- the **store model** (`Engine.Model.run`, with `DB`, `HeldM` and their
  operations): SQLite's reads and writes answer as the model's tables.
  Tested row for row (tests/engine/Differential.lean), not proven. Laws
  5–8, 11 and 18 depend on it.
- **`Unforgeable`**: Ed25519 unforgeability over one store's
  signatures. Law 1.
- **`Distinct`** (from `CollisionFree`): no SHA-256 collision among the
  ops a node received. Law 11.
- **`sym`**: the symbolic model of the cryptography. Laws 9 and 10.

The cost law (17) also rests on the meter's erasure equations, which are
proven. The generated section below lists the 50 definitions.

## Also considered

All of these are wired (about running code) and use only the standard
axioms. Each is left out because a top law covers it, it depends on
more, its running path is not complete, or a user sees it less. 🟡
marks a law whose README row says what is still missing.

### Security and the engine

| Law, in plain words | Lean name | Example | Why not in the top list |
|---|---|---|---|
| Nobody can rename an op: its id is the hash of its exact bytes. | `Op.id_decode` | kernel | Dropped by the user. Control: a trailing byte is rejected (`encode_decode`). |
| Removing someone takes two confirmations. | `writes_only_after_two` | kernel | Dropped by the user. Control: the first yes writes nothing. |
| Every valid message verifies under its author's admitted device key, with no assumption. | `message_authorized` | runtime | 1 says more; this one needs no `Unforgeable`. A good alternative to 1. |
| A removal cuts off the removed user's node. | `removal_cuts_off` | runtime | A consequence of the trust rule's law (5). |
| A removal does not change past verdicts. | `valid_stays` | runtime | Less central to a user than 4. |
| Per connection step, a refused peer gets only the notice. | `removed_gets_only_notice` | runtime | The one-step form of 6, with a smaller surface (7). |
| Every connection step reads its rooms afresh. | `entry_fresh` | runtime | The base of 6. |
| Sync advertises only stored shared ops of the connection's rooms. | `offer_shared` | kernel | The advertising half of 7. |
| A session takes in only ops of its rooms. | `recv_take` | kernel | The receiving half of 7. |
| A frame that does not open changes nothing (any family). | `sealed_unopened` | kernel | The generic form of 8. |
| A decoded value has exactly one encoding. | `Codec.encode_decode` | kernel | Goes with `Op.id_decode`. Surface: 4. |
| Taking an op in twice is taking it in once. | `ingest_twice` | kernel | Short and clear; less visible to a user. |
| A purge deletes no shared op. | `purge_shared` | runtime | Engine safety; less visible to a user. |
| At rest, the stored verdict is the spec's verdict. | `status_iff_spec` | runtime | The bridge from laws 1–4 to the store. Show it beside them. |
| A valid attachment chunk is its file's own slice. | `chunk_is_slice` | conditional | Rests on `NoCollision` and SHA-256's output size. |
| Without a session, a peer can push in only a join request. | `bare_takes_only_join` | runtime | Strong, but its surface is 500. |

### The screen

| Law, in plain words | Lean name | Example | Control | Why not in the top list |
|---|---|---|---|---|
| With the conversation at the bottom, the newest message is wholly visible, above the composer or keyboard and below the header. | `Geometry.newest_visible` | kernel | a screen that does not fit fails its premise | 🟡 Strong demo (open the keyboard). It is stated over `Seam.home`, a spec that `placed_row` ties to the running `place`: two laws to read. |
| On the emoji sheet, a tap selects exactly the key drawn there. | `SheetGeom.hit_iff` | kernel | a tap in a gap, or on the next key, is rejected | One sheet only. A good alternative to 15. |
| A tap lands on the row drawn under it. | `Geometry.pinned_tap` | kernel | — | 🟡 Stated over `tapRow`, a spec that `Input.tap_page` ties to the running code. |
| The published surface keeps the newest message visible. | `Surface.pinned_visible` | kernel | — | 🟡 The surface's form of `newest_visible`. |
| Each vsync's shift of the drawn buffer shows no blank. | `Translate.covered` | kernel | — | 🟡 Completes 13 for the shifted buffer, but its hypothesis is long. |
| Each painted position shows the right line of the right row. | `Cover.line_painted` | — | — | The companion of 13; less visible. |
| A name is marked "⚠ Duplicate" exactly when another member's name looks the same. | `ViewLaws.namesake_iff` | runtime | the mark is false before the twin, true after | 🟡 The running read is proven; the drawn mark (`row_marked`) is not wired (the message read it uses does not run). Look-alike letters across scripts are not covered. |
| The people list is exactly the present members. | `present_iff` | runtime | — | Less visible than `deviceCut_removal` (18), whose mutant is about the same lists. |
| A channel's list is in a strict order, with no ties. | `order_total` | runtime | — | Folded into 12. |
| Every community has exactly one row in the switcher. | `switcherOrder_complete`, `switcherOrder_sound` | kernel | pinned iPhone bug | Folded into 15. |
| Bidi reordering drops and invents no character. | `visual_perm` | kernel | — | 🟡 Surface 55, none spec-only. |
| Wrapping loses only spaces. | `wrap_keeps` | kernel | none yet | 🟡 Moved out for the stronger screen laws. |
| Picture bytes from a peer decode to 1–2048 pixels a side, or to nothing. | `Image.decode_sized` | kernel | — | Hostile input; surface 17, none spec-only. |
| A screen is notified exactly when a window it watches changed. | `notice_iff`, `read_notice_iff` | kernel | 3 mutants (`key_notice_imprecise`, `unnetted_imprecise`, `exact_silent`) | 🟡 Strong, with mutants, but hard to show in a demo; rests on the journal assumption (`runJ`), and the running frame's windows are wider than its rows. |
| A list changes only when a row is filed under a key it read. | `eval_stable`, `view_stable` | kernel | — | Technical; the base of `notice_iff`. |
| Every read through the cache returns its moment's answer. | `read_one_moment` | kernel | — | 🟡 Needs the snapshot and journal hypotheses. |
| What the node's channel took, then what still waits, is every write offered, in order. | `NodeOffer.offer_split` | kernel | — | 🟡 Rests on the channel's answers (`offerM`). That a frame never waits is a build check, not a law, and the law over a whole run (`offer_runs`) is a model. |
| If any queued work is on screen, the worker picks on-screen work. | `Demand.next_visible` | kernel | — | Surface 1. Hard to see in a demo; time to finish is not proven. |
| On-screen work is picked within p + 1 tries. | `Demand.selected_within` | kernel | — | 🟡 Counts tries, not time. |

### Cost

| Law, in plain words | Lean name | Example | Control | Why not in the top list |
|---|---|---|---|---|
| Judging cannot be hung: a budget read off the tables empties the queue. | `drain_bounded` | runtime | reversed order, replay | Strong against denial of service, but the budget grows with the store. |
| Judging one op costs work in its requirements, its keys and the ops that waited on it, and nothing else. | `step_costs` | — | — | Two of those counts are not capped yet (docs/PERF.md ❌ rows), so it does not yet promise a size-independent cost. |
| A list read's window holds exactly its rows. | `Engine.window_rows` | kernel | — | About which rows notices watch, not about cost. The bound on a list read is `list_costs`, which is not wired (below). |
| Every wanted op is served within its place in the queue. | `owed_within` | — | — | Sync service; rests on the store model; hard to show. |

### Not about running code yet

These would be strong headline laws, but tests/Wiring.lean classes them
as models: what they are about does not run yet, or their subject is a
specification. They are in tests/Headline.lean's last group, with
`Engine.World.Plain.converge` (every member gets every op, in a World of
n nodes running the node's code).

| Law, in plain words | Lean name | What is missing |
|---|---|---|
| Loading older messages never moves what is on screen. | `Heights.anchor_stable` | The app does not use the rows' heights tree yet (docs/PERF.md, `frame_work` ❌); `Heights.screenY` does not run. A top candidate once it does. |
| The heights tree finds a row in log₂ rows (13 steps at 5,000 rows, where the walk takes 4,981). | `Heights.T.find_spec`, `Heights.rows_cost` | Same: nothing running calls the tree yet. |
| The frame's values settle in a bounded number of reader passes. | `Live.World.settle_passes` | Stated over the board's World; the running reader and frame are being wired to it. |
| A row is drawn with "⚠ Duplicate" exactly when its name has a twin. | `ViewLaws.row_marked` | The message read it names (`Kinds.Message.read`) does not run. |
| Over any run, no write offered to the node is lost, doubled or overtaken. | `NodeOffer.offer_runs` | Its subject is a specification of runs (`NodeOffer.run`), not running code. |
| A list read costs at most limit + cap rows and 3 + limit seeks, however many rows the store holds. | `Engine.list_costs` | Stated over any store whose answers fit (`Fits`); the wiring check finds no running code in its statement. Nothing yet ties the running reader's window (200 rows) to it in one law. |
| Your own writes are served first, within two turns. | `Prioritized.write_within`, `Priority.write_within` | Stated over a model of the scheduler (`Run.selected`); the running loop uses `Inbox.Priority.next`. |

## README headline claims that need care

The README's bold list is what a judge reads first. These claims rest
on a model, on an assumption, or on unfinished work, or their wording
has gone stale. This stream did not edit the README.

1. **"honest nodes that hold the same ops agree; *(model)*"**: the
   *(model)* mark is stale. `same_ops_same_verdicts` is now wired,
   through the bridges `run_step`, `run_drain`, `run_ingest` and
   `run_purge`. It still rests on the store model and on `Distinct`.
   "Towards Proofs for n Clients" also still says "proven so far over a
   model of purging".
2. **"a removal cuts off every device of the removed user, for good"**:
   true of the devices. But the removed *user* is not out for good: its
   invitations and approvals stay Valid, so it can approve a new device
   on its own node, which the trust rule lets in (`new_device_trusted`).
   The README says this under "Not yet proven". A judge may read "for
   good" as "the person is out for good". Suggest: "cuts off every
   device of the removed user; a removed member can come back only
   through a new device (not yet prevented)".
3. **"a removal reaches every live session"**: wired for every frame
   that the node seals (`removal_reaches_session`). The table row is 🟡:
   the bare handshake replies are proven only per step (`answer_trusted`,
   `resend_trusted`), and not once the removed member admits a new
   device.
4. **"only a session's two nodes can derive its keys, even if both
   nodes' long-term keys leak after it closes"**: proven in the symbolic
   model only (`kk_forward_secret`), and it assumes that deleted bytes
   leave the disk (doubtful on journaling file systems and flash). The
   step from stored bytes to the symbolic model's names is not proven.
   The "Not yet proven" list says that `close_forgets` is not proven, but
   it is proven and wired now; what remains open is the disk, a waiting
   initiator's ephemeral key, and that step.
5. **"non-members get none of a community's ops"**: wired for ops
   (laws 7 and 5, `rooms_trusted`). Message *content* secrecy is not:
   the key-wrap writers do not read `recipients`, so `recipients_iff` is
   a model, and removed members keep old content keys (no rotation).
6. **"No session before approval"** (table) and **bootstrap
   convergence** are over models (`Net.Scene`), and the README marks
   them so.
7. **"Not yet proven: that every member eventually gets every op:
   proven so far for two nodes, over a model"**: partly stale. The
   n-node World now runs n copies of the node's code (`converge`,
   `offline`), but in a World, not yet wired.
8. **The store model in general.** 424 laws take `Model.run`: they are
   about the app's code run on a model of SQLite, not on SQLite. The
   README says so under "What is Assumed", but not in the bold list.
   Six of the eighteen depend on it.

## Surfaces too big to review

Most surfaces look big (300 or more) because the law is about a large
part of the app: the whole Community validator, or the node. That part
is code that runs, which the law covers. The spec-only part is what a
reviewer reads, and for most laws it is under ten definitions. These
are the exceptions. Each suggestion is a **proposal only**; no law was
changed.

- **`removal_reaches_session`** (613; 13 spec-only predicates, 24
  assumed, 5 bridged). It has five hypotheses about the node's hooks,
  and its conclusion goes through `FramesBy` and `MayGo` to
  `NoticeOnly`, `Owed`, `Refused` and `ReachIn`.
  - Bundle the three read-only hypotheses (`hfr`, `hc`, `hs`) into one
    named predicate, as `entry_fresh` bundles its own into
    `ReadOnly x`.
  - Inline `MayGo` in the conclusion, so the statement itself says:
    "a sync wire op, an op of another room, or an op in the closure of
    a removal owed to the peer".
  - Or lead with `removed_gets_only_notice` (7 spec-only), the
    per-step form, and present this law as its composition.
- **`no_impersonation`** and **`admission_needs_approval`**: small
  surfaces (6 and 8), but long statements, with eight nested
  existentials each. A named predicate for "device d signed op o" and
  one for "an approval by another admitted device" would make them
  shorter to read.
- **`connect_iff`**, **`present_iff`**: these take `Inv`, a six-part
  invariant of the tables. A corollary that takes `Reach` ("a store that
  the engine reaches by taking in ops and judging them") reads more
  simply; `reach_inv` gives `Inv` from `Reach`.
- **`bare_takes_only_join`** (500; 2 spec-only, 17 assumed): small to
  review, but a large part of the node.

## Comparator

Lean v4.35's `lake comparator` builds a challenge module (trusted
statements) and a solution module in a sandbox, exports both, and
accepts only if each named theorem has the same statement in both,
every constant those statements name is the same in both, and the
solution's proofs use only the permitted axioms. The vibecheck/toolchain
stream confirmed this shape on 4.35 with the app's own laws: an honest
pair is accepted, a weakened statement is rejected ("statement do not
match"), and a `sorry` in the solution is rejected ("Illegal axiom
sorryAx").

Two ways to judge the eighteen, both run on v4.35:

**As `Headline.<law>` (the root config, per push).** A plain
`lake comparator` at the repository's root reads
[comparator.json](../comparator.json):

- [tests/comparator/Challenge.lean](../tests/comparator/Challenge.lean):
  the eighteen statements, word for word, as `Headline.<law>`, each with
  `sorry`. It imports the modules that hold the laws; the judged names
  are new, so nothing is declared twice.
- [tests/comparator/Solution.lean](../tests/comparator/Solution.lean):
  the same statements, copied by tests/comparator/solution.py, each
  proved by its law.
- [tests/comparator/Check.lean](../tests/comparator/Check.lean): checks
  that each statement is the law's own (`#same_statement`, which also
  pairs the matcher that a `match` in a statement makes), so Comparator's
  match with the challenge is a match with the law, and the kernel checks
  the law's own proof. It prints the axioms.
- [tests/comparator/Weak.lean](../tests/comparator/Weak.lean) and
  comparator-weak.json: the control, the challenge with
  `removal_authorized` weakened to `t = u ∨ True`, which Comparator must
  reject.

**Under the laws' own names (nightly).** Each challenge in
tests/comparator/own/ states its laws under their own names and imports
only modules that define what the statements name: none holds or imports
one of its laws. To make that possible for every law, these definitions
moved (approved by the user; no theorem moved and no statement changed;
modules that import a law's module still get them):

| Law | Definitions moved | From | To |
|---|---|---|---|
| `removed_stays` | `Removed`, `Member`, `Live`, `Cut` | app/community/member/remove/Proofs.lean | app/community/Family.lean, beside `V` and `Admitted` |
| `removal_reaches_session` | `MayGo` | app/Proofs.lean | app/connection/Proofs.lean, beside `LiveIn` and `NoticeOnly` |
| `recv_send` | `Sendable`, `Takeable` | engine/sync/ConnLaws.lean | engine/sync/Conn.lean, beside `Conn.shows` |
| `kk_secret`, `kk_authentic` | the symbolic model: `T`, `dh`, `dec`, `unpair`, `sym`, `Sends`, `Reveals`, `Derivable`, `Clean`, `Exposed`, `secrets`, `Part`, `Answers` | engine/wire/NoiseSymbolic.lean | engine/wire/NoiseModel.lean (new) |
| `display_agrees` | `Posted` | app/community/channel/message/Proofs.lean | app/community/channel/message/receipt/Proofs.lean, beside `Listed` |
| `Cover.covered` | `Px`, `find`, `seen` | engine/renderer/Cover.lean | engine/renderer/CoverSeen.lean (new) |

After the moves, ci/layout.py passes, tests/Wiring.lean classifies all
1,413 laws exactly as before (same class, subject and missing links for
each), the README's wiring block is unchanged, its links are regenerated
(`Symbolic.sym` now points into NoiseModel.lean), and `lake check`
passes. `#challenge_imports` (tests/SpecSurface.lean; run by
tests/comparator/Feasible.lean) finds all eighteen free, and groups them,
first fit, into five challenges whose imports reach none of their own
laws:

| Config | Laws, under their own names |
|---|---|
| tests/comparator/own-community.json | `no_impersonation`, `admission_needs_approval`, `removal_authorized`, `removed_stays`, `connect_iff`, `kk_secret`, `kk_authentic`, `display_agrees`, `Cover.covered`, `approveReq_ops`, `deviceCut_removal` |
| tests/comparator/own-app.json | `removal_reaches_session`, `back_open` |
| tests/comparator/own-engine.json | `recv_send`, `same_ops_same_verdicts` |
| tests/comparator/own-connection.json | `sealed_auth`, `select_tapped_dedupe` |
| tests/comparator/own-cost.json | `ingest_costs` |

Fewer would need import changes: `app.community.Op` imports the
`engine.core.Engine` umbrella, which imports the laws of
`same_ops_same_verdicts` and `ingest_costs`; `engine.core.CostStore`
imports Termination through `engine.core.Held` and Budget; and
`app.connection.Family` reaches member/remove/Proofs.lean. `back_open`
needs `app.Screen`, which imports most of the app.

**Results on v4.35:** see the [gate](#in-the-gate) below for when each
runs. `lake comparator` accepts the root config ("Your solution is
okay!") and every own-name config, and rejects the control ("Challenge
and solution theorem statement do not match:
'Headline.removal_authorized'").

The comparator modules are the `Comparator` library, which is never a
default target, so `lake build` and `lake check` never see a `sorry`.
Comparator does not check the runtime examples, which run native code.
Kernel examples, with a toy `Crypto` as in tests/vacuity/Contracts.lean,
would let laws 2–6, 8, 11, 12, 14 and 18 show satisfiable hypotheses in
the kernel.

### In the gate

- **Per push** (ci/local.sh's parallel phase, part `headline`,
  `mise run test:headline`): tests/Headline.lean, this page's generated
  section, the challenge, solution and checks, `lake comparator` on the
  root config, and its weakened control. Its other controls: a weakened
  restatement and a changed `match` must fail `#same_statement`, and
  `#headline` must fail on a law that rests on `sorry`.
- **Nightly** (`ci/local.sh --full`, part `headline:own`,
  `mise run test:headline-own`): every law can be stated with
  definitions only, and `lake comparator` accepts the five own-name
  configs.

The `headline` part runs beside the other fast parts. Comparator builds
the two modules in its sandbox with `lake build`, which may write only
the checkout's `.lake`; after the gate's build part every module is
built, so that build only reads, as the other fast parts' `lake build`s
do (Lake takes no lock on builds).

Measured on 2026-11-01, warm, with the box's load at 60–75: the
`headline` part took 89 s and 170 s in two gate runs, and each time
ended before `engine:suites` (108 s, 185 s), which still sets the
parallel phase's length. A gate run without the part took 229 s, with
it 337 s and 392 s, but the parts it does not touch (`readme`, in the
sequential phase) varied as much (58 s to 146 s): the change is within
the load's noise. In the sequential phase the part would add its whole
time.

## Surfaces (generated)

The numbers and lists below are tests/Headline.lean's output, written
by ci/headline.py. Do not edit them by hand. The app's part of each
recommended law, and the details of every other law above, are in
[HEADLINE-SURFACES.md](HEADLINE-SURFACES.md).

<!-- surface:begin: written by ci/headline.py; do not edit -->

### Recommended

| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |
|---|---|---|---:|---:|---:|---:|---:|
| [`no_impersonation`](#communityno_impersonation) | [app/community/Proofs.lean:121](../app/community/Proofs.lean#L121) | propext, Classical.choice, Quot.sound | 367 | 345 | 6 | 1 | 1 |
| [`admission_needs_approval`](#communityadmission_needs_approval) | [app/community/member/invite/Proofs.lean:44](../app/community/member/invite/Proofs.lean#L44) | propext, Classical.choice, Quot.sound | 352 | 344 | 8 | 0 | 0 |
| [`removal_authorized`](#communityremoval_authorized) | [app/community/member/Proofs.lean:51](../app/community/member/Proofs.lean#L51) | propext, Classical.choice, Quot.sound | 352 | 344 | 8 | 0 | 0 |
| [`removed_stays`](#communityremoved_stays) | [app/community/member/remove/Proofs.lean:10](../app/community/member/remove/Proofs.lean#L10) | propext, Classical.choice, Quot.sound | 351 | 344 | 7 | 0 | 0 |
| [`connect_iff`](#communityconnect_iff) | [app/community/Proofs.lean:823](../app/community/Proofs.lean#L823) | propext, Classical.choice, Quot.sound | 399 | 377 | 10 | 0 | 1 |
| [`removal_reaches_session`](#connectionremoval_reaches_session) | [app/Proofs.lean:3012](../app/Proofs.lean#L3012) | propext, Classical.choice, Quot.sound | 672 | 636 | 16 | 6 | 1 |
| [`recv_send`](#enginesyncrecv_send) | [engine/sync/ConnLaws.lean:185](../engine/sync/ConnLaws.lean#L185) | propext, Classical.choice, Quot.sound | 166 | 154 | 5 | 5 | 0 |
| [`sealed_auth`](#connectionsealed_auth) | [app/connection/Proofs.lean:160](../app/connection/Proofs.lean#L160) | propext, Classical.choice, Quot.sound | 371 | 349 | 4 | 5 | 0 |
| [`kk_secret`](#connectionnoisesymbolickk_secret) | [engine/wire/NoiseSymbolic.lean:510](../engine/wire/NoiseSymbolic.lean#L510) | propext, Quot.sound | 29 | 18 | 7 | 1 | 0 |
| [`kk_authentic`](#connectionnoisesymbolickk_authentic) | [engine/wire/NoiseSymbolic.lean:801](../engine/wire/NoiseSymbolic.lean#L801) | propext, Quot.sound | 30 | 18 | 8 | 1 | 0 |
| [`same_ops_same_verdicts`](#enginesame_ops_same_verdicts) | [engine/core/Termination.lean:122](../engine/core/Termination.lean#L122) | propext, Classical.choice, Quot.sound | 68 | 63 | 2 | 1 | 0 |
| [`display_agrees`](#communitydisplay_agrees) | [app/community/channel/message/Proofs.lean:198](../app/community/channel/message/Proofs.lean#L198) | propext, Classical.choice, Quot.sound | 361 | 353 | 8 | 0 | 0 |
| [`Cover.covered`](#covercovered) | [engine/renderer/Cover.lean:53](../engine/renderer/Cover.lean#L53) | propext, Quot.sound | 3 | 3 | 0 | 0 | 0 |
| [`back_open`](#navlawsback_open) | [app/Proofs.lean:1320](../app/Proofs.lean#L1320) | propext, Classical.choice, Quot.sound | 755 | 749 | 2 | 0 | 0 |
| [`select_tapped_dedupe`](#switchselect_tapped_dedupe) | [app/community/Screen.lean:812](../app/community/Screen.lean#L812) | propext, Quot.sound | 9 | 9 | 0 | 0 | 0 |
| [`approveReq_ops`](#communityapprovereq_ops) | [app/community/Proofs.lean:1329](../app/community/Proofs.lean#L1329) | propext, Classical.choice, Quot.sound | 195 | 193 | 2 | 0 | 0 |
| [`ingest_costs`](#engineingest_costs) | [engine/core/IngestCost.lean:49](../engine/core/IngestCost.lean#L49) | propext, Classical.choice, Quot.sound | 46 | 32 | 6 | 0 | 8 |
| [`deviceCut_removal`](#peoplelawsdevicecut_removal) | [app/community/Screen.lean:606](../app/community/Screen.lean#L606) | propext, Classical.choice, Quot.sound | 109 | 92 | 2 | 0 | 1 |

**Together** these laws name 54 spec-only definitions, and 10 names of the assumptions they take.

<details><summary>The spec-only definitions, together</summary>

- predicates: `Community.Admitted`, `Community.IsAdmin`, `Community.Keyed`, `Community.Listed`, `Community.Live`, `Community.Posted`, `Community.Removed`, `Community.V`, `Connection.LiveIn`, `Connection.MayGo`, `Connection.Noise.Symbolic.Answers`, `Connection.Noise.Symbolic.Clean`, `Connection.Noise.Symbolic.Derivable`, `Connection.Noise.Symbolic.Exposed`, `Connection.Noise.Symbolic.Part`, `Connection.Noise.Symbolic.Reveals`, `Connection.Noise.Symbolic.Sends`, `Connection.Noise.Symbolic.secrets`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Costs`, `Engine.Extends`, `Engine.Field`, `Engine.Inv`, `Engine.Reach`, `Engine.Spec`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.Key.lt`, `Engine.Sync.Key.plt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReachIn`, `Engine.Sync.Reads`, `Engine.Sync.Sendable`, `Engine.Sync.Sorted`, `Engine.View.Always`, `Engine.Within`, `Ttf.Bitmap.Valid`
- types: `Connection.Noise.Symbolic.T`, `Engine.Sync.ReadsOnly`
- definitions: `Community.Fact.admin`, `Community.Fact.admission`, `Community.Fact.approval`, `Community.Fact.message`, `Community.Fact.received`, `Community.Fact.removal`, `Community.Fact.request`, `Engine.specAt`
- instances: `Connection.Noise.Symbolic.instDecidableEqT`, `Engine.Meter.instAdd`, `Engine.Meter.instOfNatOfNatNat`
- assumed: `Community.Unforgeable`, `Connection.Noise.Symbolic.sym`, `Engine.DB.deleteOp`, `Engine.DB.undecide`, `Engine.Distinct`, `Engine.Model.pop`, `Engine.Sync.instReadsOnlyHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.instMonadModel`, `Engine.modelStore`

</details>

#### Community.no_impersonation

Named in the statement: `Community.Body`, `Community.Body.post`, `Community.Crypto`, `Community.Fact.admission`, `Community.Fact.message`, `Community.Key`, `Community.Unforgeable`, `Community.V`, `Community.instCodecBody`, `Community.signed`, `Engine.Codec.decode`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.message`, `Engine.specAt`.

Assumed: `Community.Unforgeable`. Bridged: `Community.signed` (by `Community.signed_eq`).

#### Community.admission_needs_approval

Named in the statement: `Community.Crypto`, `Community.Fact.admission`, `Community.Fact.approval`, `Community.Fact.request`, `Community.Key`, `Community.Keyed`, `Community.V`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.Keyed`, `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.approval`, `Community.Fact.request`, `Engine.specAt`.

Assumed: none. Bridged: none.

#### Community.removal_authorized

Named in the statement: `Community.Crypto`, `Community.Fact.removal`, `Community.IsAdmin`, `Community.V`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.IsAdmin`, `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.admin`, `Community.Fact.admission`, `Community.Fact.removal`, `Engine.specAt`.

Assumed: none. Bridged: none.

#### Community.removed_stays

Named in the statement: `Community.Crypto`, `Community.Removed`, `Engine.Extends`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.Removed`, `Community.V`, `Engine.Codec.At`, `Engine.Extends`, `Engine.Spec`; definitions: `Community.Fact.removal`, `Engine.specAt`.

Assumed: none. Bridged: none.

#### Community.connect_iff

Named in the statement: `Community.Admitted`, `Community.Crypto`, `Community.Fact`, `Community.Key`, `Community.Live`, `Community.allowPeer`, `Community.family`, `Community.instSortKeyFact`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Engine.View.eval`.

Spec-only, to review: predicates: `Community.Admitted`, `Community.Live`, `Community.Removed`, `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.removal`, `Engine.specAt`.

Assumed: none. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Connection.removal_reaches_session

Named in the statement: `Community.Fact`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.Keys`, `Connection.MayGo`, `Connection.hooks`, `Connection.instSortKeyFact`, `Engine.Fresh`, `Engine.Id`, `Engine.Op`, `Engine.Sync.Catalog`, `Engine.Sync.Effects`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.Hooks`, `Engine.Sync.Moves`, `Engine.Sync.Node`, `Engine.Sync.Reads`, `Engine.Sync.RetryStore`, `Engine.Sync.Sweep`, `Engine.Sync.Sync`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instReadsOnlyHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.instSortKeySum`.

Spec-only, to review: predicates: `Connection.LiveIn`, `Connection.MayGo`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.Key.lt`, `Engine.Sync.Key.plt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReachIn`, `Engine.Sync.Reads`, `Engine.Sync.Sorted`; types: `Engine.Sync.ReadsOnly`.

Assumed: `Engine.DB.deleteOp`, `Engine.DB.undecide`, `Engine.Model.pop`, `Engine.Sync.instReadsOnlyHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.modelStore`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Engine.Sync.recv_send

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.recv`, `Engine.Sync.Index`, `Engine.Sync.Sendable`, `Engine.Sync.Step`, `Engine.instMonadModel`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.Key.plt`, `Engine.Sync.Sendable`, `Engine.Sync.Sorted`.

Assumed: `Engine.DB.deleteOp`, `Engine.DB.undecide`, `Engine.Model.pop`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Connection.sealed_auth

Named in the statement: `Community.Fact`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.Frame.ad`, `Connection.Frame.cid`, `Connection.Keys`, `Connection.instSortKeyFact`, `Connection.openFrame`, `Connection.sessionKeys`, `Engine.Id`, `Engine.Sync.Effects`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.Node`, `Engine.Sync.Node.onFrame`, `Engine.Sync.RetryTicket`, `Engine.Sync.Sync`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.sealedTag`, `Engine.Sync.tagged`, `Engine.instSortKeySum`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.Key.plt`, `Engine.Sync.Sorted`.

Assumed: `Engine.DB.deleteOp`, `Engine.DB.undecide`, `Engine.Model.pop`, `Engine.Sync.instStoreHeldM`, `Engine.modelStore`. Bridged: none.

#### Connection.Noise.Symbolic.kk_secret

Named in the statement: `Connection.Noise.Session`, `Connection.Noise.Sym`, `Connection.Noise.Symbolic.Derivable`, `Connection.Noise.Symbolic.Exposed`, `Connection.Noise.Symbolic.T`, `Connection.Noise.Symbolic.instDecidableEqT`, `Connection.Noise.Symbolic.secrets`, `Connection.Noise.Symbolic.sym`, `Connection.Noise.read1`, `Connection.Noise.read2`, `Connection.Noise.sent1`, `Connection.Noise.write2`.

Spec-only, to review: predicates: `Connection.Noise.Symbolic.Derivable`, `Connection.Noise.Symbolic.Exposed`, `Connection.Noise.Symbolic.Reveals`, `Connection.Noise.Symbolic.Sends`, `Connection.Noise.Symbolic.secrets`; types: `Connection.Noise.Symbolic.T`; instances: `Connection.Noise.Symbolic.instDecidableEqT`.

Assumed: `Connection.Noise.Symbolic.sym`. Bridged: none.

#### Connection.Noise.Symbolic.kk_authentic

Named in the statement: `Connection.Noise.Session`, `Connection.Noise.Sym`, `Connection.Noise.Symbolic.Answers`, `Connection.Noise.Symbolic.Clean`, `Connection.Noise.Symbolic.Derivable`, `Connection.Noise.Symbolic.Part`, `Connection.Noise.Symbolic.T`, `Connection.Noise.Symbolic.instDecidableEqT`, `Connection.Noise.Symbolic.sym`, `Connection.Noise.read2`, `Connection.Noise.sent1`.

Spec-only, to review: predicates: `Connection.Noise.Symbolic.Answers`, `Connection.Noise.Symbolic.Clean`, `Connection.Noise.Symbolic.Derivable`, `Connection.Noise.Symbolic.Part`, `Connection.Noise.Symbolic.Reveals`, `Connection.Noise.Symbolic.Sends`; types: `Connection.Noise.Symbolic.T`; instances: `Connection.Noise.Symbolic.instDecidableEqT`.

Assumed: `Connection.Noise.Symbolic.sym`. Bridged: none.

#### Engine.same_ops_same_verdicts

Named in the statement: `Engine.DB`, `Engine.Distinct`, `Engine.Family`, `Engine.Id`, `Engine.Op`, `Engine.Reach`, `Engine.Verdict`, `Engine.drainS`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Reach`.

Assumed: `Engine.Distinct`. Bridged: none.

#### Community.display_agrees

Named in the statement: `Community.Crypto`, `Community.Listed`, `Community.Posted`, `Community.countCap`, `Engine.Id`, `Engine.Op`, `Engine.Pos.cmp`.

Spec-only, to review: predicates: `Community.Listed`, `Community.Posted`, `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.message`, `Community.Fact.received`, `Engine.specAt`.

Assumed: none. Bridged: none.

#### Cover.covered

Named in the statement: `Cover.Px`, `Cover.seen`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### NavLaws.back_open

Named in the statement: `App.PageId`, `App.PageId.code`, `App.PageIn`, `App.Presentation.Entry`, `App.Presentation.capacity`, `App.PresentationCandidate`, `App.St`, `App.St.nav`, `App.backSt`, `App.instDecidableEqPageId`, `App.openSt`, `Data.placeIn`, `Nav.go`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Ttf.Bitmap.Valid`.

Assumed: none. Bridged: none.

#### Switch.select_tapped_dedupe

Named in the statement: `Kinds.Accepted.Me`, `Kinds.Accepted.dedupe`, `Kinds.Accepted.select`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Community.approveReq_ops

Named in the statement: `Community.Device`, `Community.Fact`, `Community.Write`, `Community.approveReq`, `Engine.Id`, `Engine.Op`, `Engine.View.Always`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.View.Always`.

Assumed: none. Bridged: none.

#### Engine.ingest_costs

Named in the statement: `Engine.CostT`, `Engine.CostT.instMonad`, `Engine.Costs`, `Engine.Op`, `Engine.Store`, `Engine.ingest`, `Engine.instStoreCostT`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Costs`, `Engine.Field`, `Engine.Within`; instances: `Engine.Meter.instAdd`, `Engine.Meter.instOfNatOfNatNat`.

Assumed: none. Bridged: `Engine.CostT` (the cost meter), `Engine.CostT.bind` (by `Engine.CostT.erase_bind`), `Engine.CostT.charged` (by `Engine.CostT.erase_charged`), `Engine.CostT.chargedBy` (by `Engine.CostT.erase_chargedBy`), `Engine.CostT.instMonad` (the cost meter), `Engine.CostT.pure` (by `Engine.CostT.erase_pure`), `Engine.CostT.run` (by `Engine.CostT.erase_run`), `Engine.instStoreCostT` (the cost meter).

#### PeopleLaws.deviceCut_removal

Named in the statement: `Community.Fact`, `Community.Fact.admission`, `Community.Key`, `Community.admission.byDevice`, `Community.deviceCut`, `Community.instSortKeyFact`, `Community.removals`, `Engine.Answer`, `Engine.DB`, `Engine.Id`, `Engine.Pos`, `Engine.Rel.read`, `Engine.View.eval`, `Engine.eval`.

Spec-only, to review: predicates: `Engine.Codec.At`; definitions: `Community.Fact.admission`.

Assumed: none. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

### Also considered

| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |
|---|---|---|---:|---:|---:|---:|---:|
| [`id_decode`](HEADLINE-SURFACES.md#engineopid_decode) | [engine/core/Core.lean:94](../engine/core/Core.lean#L94) | propext, Classical.choice, Quot.sound | 35 | 34 | 1 | 0 | 0 |
| [`writes_only_after_two`](HEADLINE-SURFACES.md#removewrites_only_after_two) | [app/community/member/remove/View.lean:61](../app/community/member/remove/View.lean#L61) | propext, Quot.sound | 4 | 4 | 0 | 0 | 0 |
| [`wrap_keeps`](HEADLINE-SURFACES.md#textwrap_keeps) | [engine/renderer/WrapLaws.lean:134](../engine/renderer/WrapLaws.lean#L134) | propext, Classical.choice, Quot.sound | 69 | 67 | 2 | 0 | 0 |
| [`message_authorized`](HEADLINE-SURFACES.md#communitymessage_authorized) | [app/community/channel/message/Proofs.lean:73](../app/community/channel/message/Proofs.lean#L73) | propext, Classical.choice, Quot.sound | 365 | 345 | 6 | 0 | 1 |
| [`removal_cuts_off`](HEADLINE-SURFACES.md#communityremoval_cuts_off) | [app/community/Proofs.lean:920](../app/community/Proofs.lean#L920) | propext, Classical.choice, Quot.sound | 398 | 377 | 9 | 0 | 1 |
| [`valid_stays`](HEADLINE-SURFACES.md#communityvalid_stays) | [app/community/Family.lean:1410](../app/community/Family.lean#L1410) | propext, Classical.choice, Quot.sound | 349 | 344 | 5 | 0 | 0 |
| [`removed_gets_only_notice`](HEADLINE-SURFACES.md#connectionremoved_gets_only_notice) | [app/Proofs.lean:211](../app/Proofs.lean#L211) | propext, Classical.choice, Quot.sound | 331 | 306 | 9 | 5 | 1 |
| [`entry_fresh`](HEADLINE-SURFACES.md#enginesyncentry_fresh) | [engine/wire/EgressLaws.lean:963](../engine/wire/EgressLaws.lean#L963) | propext, Classical.choice, Quot.sound | 322 | 299 | 13 | 6 | 0 |
| [`offer_shared`](HEADLINE-SURFACES.md#enginesyncoffer_shared) | [engine/sync/SecrecyLaws.lean:64](../engine/sync/SecrecyLaws.lean#L64) | propext, Classical.choice, Quot.sound | 89 | 81 | 1 | 5 | 0 |
| [`recv_take`](HEADLINE-SURFACES.md#enginesyncrecv_take) | [engine/sync/ConnLaws.lean:152](../engine/sync/ConnLaws.lean#L152) | propext, Classical.choice, Quot.sound | 166 | 154 | 5 | 5 | 0 |
| [`sealed_unopened`](HEADLINE-SURFACES.md#enginesyncsealed_unopened) | [engine/wire/NodeLaws.lean:70](../engine/wire/NodeLaws.lean#L70) | propext, Classical.choice, Quot.sound | 280 | 267 | 4 | 5 | 0 |
| [`encode_decode`](HEADLINE-SURFACES.md#enginecodecencode_decode) | [engine/core/Codec.lean:775](../engine/core/Codec.lean#L775) | propext | 4 | 3 | 1 | 0 | 0 |
| [`drain_bounded`](HEADLINE-SURFACES.md#enginedrain_bounded) | [engine/core/Budget.lean:167](../engine/core/Budget.lean#L167) | propext, Classical.choice, Quot.sound | 71 | 64 | 2 | 1 | 0 |
| [`ingest_twice`](HEADLINE-SURFACES.md#engineingest_twice) | [engine/core/IdemLaws.lean:50](../engine/core/IdemLaws.lean#L50) | propext, Classical.choice, Quot.sound | 51 | 42 | 1 | 5 | 0 |
| [`purge_shared`](HEADLINE-SURFACES.md#enginepurge_shared) | [engine/core/Purge.lean:578](../engine/core/Purge.lean#L578) | propext, Classical.choice, Quot.sound | 47 | 44 | 1 | 0 | 0 |
| [`status_iff_spec`](HEADLINE-SURFACES.md#enginestatus_iff_spec) | [engine/core/Proofs.lean:484](../engine/core/Proofs.lean#L484) | propext, Classical.choice, Quot.sound | 42 | 38 | 4 | 0 | 0 |
| [`chunk_is_slice`](HEADLINE-SURFACES.md#communitychunk_is_slice) | [app/community/channel/message/attachment/chunk/Proofs.lean:51](../app/community/channel/message/attachment/chunk/Proofs.lean#L51) | propext, Classical.choice, Quot.sound | 216 | 206 | 3 | 1 | 0 |
| [`bare_takes_only_join`](HEADLINE-SURFACES.md#connectionbare_takes_only_join) | [app/Proofs.lean:611](../app/Proofs.lean#L611) | propext, Classical.choice, Quot.sound | 550 | 531 | 2 | 5 | 0 |
| [`order_total`](HEADLINE-SURFACES.md#communityorder_total) | [app/community/Proofs.lean:1491](../app/community/Proofs.lean#L1491) | propext, Classical.choice, Quot.sound | 400 | 386 | 5 | 0 | 1 |
| [`present_iff`](HEADLINE-SURFACES.md#peoplelawspresent_iff) | [app/community/Screen.lean:441](../app/community/Screen.lean#L441) | propext, Classical.choice, Quot.sound | 401 | 379 | 10 | 0 | 1 |
| [`namesake_iff`](HEADLINE-SURFACES.md#viewlawsnamesake_iff) | [app/community/Screen.lean:286](../app/community/Screen.lean#L286) | propext, Classical.choice, Quot.sound | 396 | 377 | 9 | 0 | 0 |
| [`Translate.covered`](HEADLINE-SURFACES.md#translatecovered) | [engine/renderer/TranslateLaws.lean:83](../engine/renderer/TranslateLaws.lean#L83) | propext, Quot.sound | 9 | 6 | 3 | 0 | 0 |
| [`line_painted`](HEADLINE-SURFACES.md#coverline_painted) | [engine/renderer/Cover.lean:93](../engine/renderer/Cover.lean#L93) | propext, Quot.sound | 3 | 3 | 0 | 0 | 0 |
| [`newest_visible`](HEADLINE-SURFACES.md#geometrynewest_visible) | [engine/renderer/Geometry.lean:105](../engine/renderer/Geometry.lean#L105) | propext, Classical.choice, Quot.sound | 5 | 3 | 2 | 0 | 0 |
| [`pinned_visible`](HEADLINE-SURFACES.md#surfacepinned_visible) | [engine/renderer/Surface.lean:141](../engine/renderer/Surface.lean#L141) | propext, Classical.choice, Quot.sound | 11 | 10 | 1 | 0 | 0 |
| [`pinned_tap`](HEADLINE-SURFACES.md#geometrypinned_tap) | [engine/renderer/Geometry.lean:158](../engine/renderer/Geometry.lean#L158) | propext, Quot.sound | 6 | 4 | 2 | 0 | 0 |
| [`hit_iff`](HEADLINE-SURFACES.md#sheetgeomhit_iff) | [engine/renderer/SheetGeom.lean:125](../engine/renderer/SheetGeom.lean#L125) | propext, Quot.sound | 8 | 4 | 2 | 0 | 1 |
| [`switcherOrder_complete`](HEADLINE-SURFACES.md#pagesswitcherorder_complete) | [app/community/Screen.lean:1099](../app/community/Screen.lean#L1099) | propext, Quot.sound | 2 | 2 | 0 | 0 | 0 |
| [`switcherOrder_sound`](HEADLINE-SURFACES.md#pagesswitcherorder_sound) | [app/community/Screen.lean:1092](../app/community/Screen.lean#L1092) | propext, Quot.sound | 2 | 2 | 0 | 0 | 0 |
| [`visual_perm`](HEADLINE-SURFACES.md#textvisual_perm) | [engine/renderer/TextLaws.lean:21](../engine/renderer/TextLaws.lean#L21) | propext, Classical.choice, Quot.sound | 55 | 55 | 0 | 0 | 0 |
| [`decode_sized`](HEADLINE-SURFACES.md#imagedecode_sized) | [engine/renderer/ImageLaws.lean:13](../engine/renderer/ImageLaws.lean#L13) | propext, Classical.choice, Quot.sound | 17 | 17 | 0 | 0 | 0 |
| [`notice_iff`](HEADLINE-SURFACES.md#enginenotice_iff) | [engine/core/WindowLaws.lean:705](../engine/core/WindowLaws.lean#L705) | propext, Classical.choice, Quot.sound | 114 | 69 | 11 | 1 | 0 |
| [`read_notice_iff`](HEADLINE-SURFACES.md#engineread_notice_iff) | [engine/core/WindowRead.lean:417](../engine/core/WindowRead.lean#L417) | propext, Classical.choice, Quot.sound | 119 | 71 | 10 | 1 | 0 |
| [`view_stable`](HEADLINE-SURFACES.md#engineview_stable) | [engine/core/View.lean:164](../engine/core/View.lean#L164) | propext, Classical.choice, Quot.sound | 74 | 56 | 6 | 0 | 1 |
| [`eval_stable`](HEADLINE-SURFACES.md#engineeval_stable) | [engine/core/View.lean:141](../engine/core/View.lean#L141) | propext, Classical.choice, Quot.sound | 71 | 55 | 5 | 0 | 0 |
| [`read_one_moment`](HEADLINE-SURFACES.md#livelawsread_one_moment) | [app/Commands.lean:1037](../app/Commands.lean#L1037) | propext, Classical.choice, Quot.sound | 74 | 71 | 3 | 0 | 0 |
| [`offer_split`](HEADLINE-SURFACES.md#nodeofferoffer_split) | [app/Screen.lean:398](../app/Screen.lean#L398) | propext | 3 | 1 | 0 | 2 | 0 |
| [`next_visible`](HEADLINE-SURFACES.md#demandnext_visible) | [engine/renderer/Demand.lean:149](../engine/renderer/Demand.lean#L149) | propext, Quot.sound | 1 | 1 | 0 | 0 | 0 |
| [`selected_within`](HEADLINE-SURFACES.md#demandselected_within) | [engine/renderer/DemandRank.lean:138](../engine/renderer/DemandRank.lean#L138) | propext, Classical.choice, Quot.sound | 4 | 3 | 1 | 0 | 0 |
| [`window_rows`](HEADLINE-SURFACES.md#enginewindow_rows) | [engine/core/WindowRead.lean:360](../engine/core/WindowRead.lean#L360) | propext, Classical.choice, Quot.sound | 63 | 52 | 5 | 0 | 0 |
| [`step_costs`](HEADLINE-SURFACES.md#enginestep_costs) | [engine/core/IngestCost.lean:126](../engine/core/IngestCost.lean#L126) | propext, Classical.choice, Quot.sound | 61 | 44 | 9 | 0 | 8 |
| [`owed_within`](HEADLINE-SURFACES.md#enginesyncowed_within) | [engine/sync/ServeLaws.lean:459](../engine/sync/ServeLaws.lean#L459) | propext, Classical.choice, Quot.sound | 76 | 67 | 1 | 5 | 0 |

**Together** these laws name 68 spec-only definitions, and 12 names of the assumptions they take.

<details><summary>The spec-only definitions, together</summary>

- predicates: `Community.Admitted`, `Community.InOrder`, `Community.Live`, `Community.Removed`, `Community.V`, `Connection.LiveIn`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Costs`, `Engine.Extends`, `Engine.Field`, `Engine.Inv`, `Engine.Later`, `Engine.OneOpPerId`, `Engine.Reach`, `Engine.ReqsLe`, `Engine.Sat`, `Engine.Spec`, `Engine.Subs.Has`, `Engine.Subs.WF`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.FramesOk`, `Engine.Sync.Key.lt`, `Engine.Sync.Key.plt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReachIn`, `Engine.Sync.ReadOnly`, `Engine.Sync.Reads`, `Engine.Sync.Sent`, `Engine.Sync.Sorted`, `Engine.Sync.Takeable`, `Engine.WaitersLe`, `Engine.Within`, `Geometry.Geom.Fits`, `LiveLaws.Agrees`, `SheetGeom.Grid.Ok`, `SheetGeom.Grid.inBox`, `Ttf.Bitmap.Valid`
- types: `Demand.SelectionRun`, `Engine.Change`, `Engine.Sync.ReadsOnly`, `ViewLaws.Model`
- definitions: `Community.Fact.admission`, `Community.Fact.chunk`, `Community.Fact.message`, `Community.Fact.profile`, `Community.Fact.removal`, `Connection.Fact.opened`, `Engine.Change.ingests`, `Engine.View.keys`, `Engine.specAt`, `Engine.window`, `Geometry.Seam.home`, `Geometry.Seam.tapRow`, `Merkle.slices`, `Surface.Frame.row`, `Text.ns`, `Translate.position`, `Translate.seen`, `Translate.source`, `ViewLaws.nameIn`
- instances: `Engine.Meter.instAdd`, `Engine.Meter.instOfNatOfNatNat`, `ViewLaws.instReadsModel`
- assumed: `Community.ChunkSound`, `Engine.DB.deleteOp`, `Engine.DB.undecide`, `Engine.Distinct`, `Engine.Model.pop`, `Engine.Sync.instReadsOnlyHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.instMonadModel`, `Engine.modelStore`, `Engine.runJ`, `NodeOffer.Chan`, `NodeOffer.offerM`

</details>

### Not about running code yet

| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |
|---|---|---|---:|---:|---:|---:|---:|
| [`converge`](HEADLINE-SURFACES.md#engineworldplainconverge) | [engine/world/Plain.lean:203](../engine/world/Plain.lean#L203) | propext, Classical.choice, Quot.sound | 345 | 301 | 35 | 5 | 0 |
| [`anchor_stable`](HEADLINE-SURFACES.md#heightsanchor_stable) | [engine/renderer/Heights.lean:502](../engine/renderer/Heights.lean#L502) | propext, Quot.sound | 10 | 4 | 6 | 0 | 0 |
| [`find_spec`](HEADLINE-SURFACES.md#heightstfind_spec) | [engine/renderer/Heights.lean:175](../engine/renderer/Heights.lean#L175) | propext, Classical.choice, Quot.sound | 12 | 4 | 8 | 0 | 0 |
| [`rows_cost`](HEADLINE-SURFACES.md#heightsrows_cost) | [engine/renderer/Heights.lean:631](../engine/renderer/Heights.lean#L631) | propext, Classical.choice, Quot.sound | 25 | 2 | 13 | 0 | 7 |
| [`settle_passes`](HEADLINE-SURFACES.md#liveworldsettle_passes) | [engine/renderer/BoardLaws.lean:481](../engine/renderer/BoardLaws.lean#L481) | propext, Classical.choice, Quot.sound | 13 | 6 | 7 | 0 | 0 |
| [`row_marked`](HEADLINE-SURFACES.md#viewlawsrow_marked) | [app/community/Screen.lean:312](../app/community/Screen.lean#L312) | propext, Classical.choice, Quot.sound | 426 | 402 | 14 | 0 | 0 |
| [`offer_runs`](HEADLINE-SURFACES.md#nodeofferoffer_runs) | [app/Screen.lean:435](../app/Screen.lean#L435) | propext | 5 | 1 | 2 | 2 | 0 |
| [`list_costs`](HEADLINE-SURFACES.md#enginelist_costs) | [engine/core/ListCost.lean:34](../engine/core/ListCost.lean#L34) | propext, Classical.choice, Quot.sound | 21 | 8 | 9 | 0 | 4 |
| [`Prioritized.write_within`](HEADLINE-SURFACES.md#enginesyncingressprioritizedwrite_within) | [engine/wire/IngressPriorityLaws.lean:220](../engine/wire/IngressPriorityLaws.lean#L220) | propext, Quot.sound | 19 | 11 | 8 | 0 | 0 |
| [`Priority.write_within`](HEADLINE-SURFACES.md#enginesyncinboxprioritywrite_within) | [engine/wire/PriorityLaws.lean:167](../engine/wire/PriorityLaws.lean#L167) | propext, Quot.sound | 14 | 11 | 3 | 0 | 0 |

**Together** these laws name 93 spec-only definitions, and 7 names of the assumptions they take.

<details><summary>The spec-only definitions, together</summary>

- predicates: `Community.V`, `Engine.Codec.At`, `Engine.Costs`, `Engine.Field`, `Engine.Fits`, `Engine.Inv`, `Engine.Sat`, `Engine.Spec`, `Engine.Sync.Key.lt`, `Engine.Sync.Key.plt`, `Engine.Sync.Sorted`, `Engine.Within`, `Engine.World.Diam`, `Engine.World.Edge`, `Engine.World.Holds`, `Engine.World.Legal`, `Engine.World.Net.Calm`, `Engine.World.Net.Live`, `Engine.World.Net.Up`, `Engine.World.Path`, `Heights.Rows.Ok`, `Heights.T.Perfect`, `Heights.T.WF`, `Live.Board.Seen`, `Live.World.Inv`
- types: `Engine.Sync.Inbox.Priority.Run`, `Engine.Sync.Ingress.Prioritized.Run`, `Engine.Sync.Ingress.Prioritized.State`, `Engine.Sync.Setup`, `Engine.Sync.Who`, `Engine.World.Act`, `Engine.World.Exec`, `Engine.World.Net`, `Engine.World.Packet`, `Engine.World.Plain`, `Engine.World.Setup`, `Engine.World.World`, `Heights.Rows`, `Heights.T`, `Live.World`, `ViewLaws.Model`
- definitions: `Community.Fact.message`, `Community.Fact.profile`, `Engine.Sync.Inbox.Priority.Run.selected`, `Engine.Sync.Inbox.Priority.State.append`, `Engine.Sync.Ingress.Prioritized.Run.selected`, `Engine.Sync.Ingress.Prioritized.State.arrivals`, `Engine.Sync.Ingress.Prioritized.popEvent`, `Engine.Sync.Ingress.Prioritized.popWrite`, `Engine.Sync.Ingress.Prioritized.step`, `Engine.Sync.Ingress.State.arrivals`, `Engine.Sync.Node.connect`, `Engine.Sync.Setup.sync`, `Engine.Sync.plainOpen`, `Engine.Sync.plainSeal`, `Engine.World.Exec.world`, `Engine.World.Plain.setup`, `Engine.World.Plain.two`, `Engine.World.Setup.at?`, `Engine.World.World.enter`, `Engine.World.World.step`, `Engine.World.packets`, `Engine.World.plainPeek`, `Engine.World.upd`, `Engine.World.worlds`, `Engine.countCost`, `Engine.listCost`, `Engine.specAt`, `Heights.T.find`, `Heights.T.findM`, `Heights.T.mk`, `Heights.T.setM`, `Heights.T.size`, `Heights.T.start`, `Heights.T.startM`, `Heights.T.sum`, `Heights.T.toList`, `Heights.screenY`, `Kinds.Message.read`, `Kinds.React.read`, `Kinds.React.tally`, `Live.Board.apply`, `Live.World.frame`, `Live.World.marked`, `Live.World.pass`, `NodeOffer.run`, `NodeOffer.submitted`, `ViewLaws.factIn`, `ViewLaws.nameIn`
- instances: `Engine.Meter.instAdd`, `Engine.Meter.instLE`, `Engine.Meter.instOfNatOfNatNat`, `ViewLaws.instReadsModel`
- assumed: `Engine.DB.deleteOp`, `Engine.DB.undecide`, `Engine.Model.pop`, `Engine.Sync.instStoreHeldM`, `Engine.modelStore`, `NodeOffer.Chan`, `NodeOffer.offerM`

</details>

<!-- surface:end -->
