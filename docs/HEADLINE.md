# Headline laws: a proposal

**Status: a proposal. The user decides which laws are headline laws.**
Nothing here changes a law. An agent drafted this list on 2026-11-01
for the Vibecheck judges' questions ([rules](VIBECHECK-RULES.md)): are
the laws important, are they about the code itself, and do they pass
Comparator?

The app has about 1,400 audited laws. This page picks fifteen that a
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
- a **control**: a bad output that the law or its check rejects.

To check every number on this page, run `mise run test:headline`
(tests/headline.sh). It builds the tree, runs tests/Headline.lean,
checks that this page's generated section is current
(ci/headline.py), and checks the draft Comparator files.

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
- **Bridged:** a copy of running code that a law proves equal to it
  (`stepS` is the engine's `step` on the store model, by `run_step`).
  The walk stops at it, because its body is the running code's.

"Surface" in the tables is the whole walk, as CLAUDE.md's
`#spec_surface` defines it. "Review" is the spec-only part plus the
assumptions.

## The recommended fifteen, ranked

| # | The law, in plain words | Lean name | Class | Review | Example | Control |
|---|---|---|---|---|---|---|
| 1 | Nobody can post as another user. | [`no_impersonation`](../app/community/Proofs.lean#L120) | wired | 6 + `Unforgeable` | conditional | forged post rejected |
| 2 | Nobody joins without a member's approval. | [`admission_needs_approval`](../app/community/member/invite/Proofs.lean#L44) | wired | 8 | runtime | 4 bad joins rejected |
| 3 | Only admins remove other members. | [`removal_authorized`](../app/community/member/Proofs.lean#L50) | wired | 8 | runtime | unauthorized removal rejected |
| 4 | A removal cannot be undone. | [`removed_stays`](../app/community/member/remove/Proofs.lean#L28) | wired | 7 | runtime | none |
| 5 | The node connects only to live members. | [`connect_iff`](../app/community/Proofs.lean#L821) | wired | 10 + store model | runtime | refused after removal |
| 6 | After a removal, the removed member gets only the notice. | [`removal_reaches_session`](../app/Proofs.lean#L3088) | wired | 13 + store model | runtime | message withheld |
| 7 | A session sends only what its peer may see. | [`recv_send`](../engine/sync/ConnLaws.lean#L158) | wired | 3 + store model | kernel | none yet |
| 8 | The node checks a frame before it reads it. | [`sealed_auth`](../app/connection/Proofs.lean#L134) | wired | 2 + store model | runtime | 3 damaged frames rejected |
| 9 | Nobody can rename an op. | [`Op.id_decode`](../engine/core/Core.lean#L93) | wired | 1 | kernel | extra byte rejected |
| 10 | Session keys stay secret. | [`kk_secret`](../engine/wire/NoiseSymbolic.lean#L633) | wired, symbolic | 7 + `sym` | kernel | tight: a leak breaks it |
| 11 | The dialer knows who answered. | [`kk_authentic`](../engine/wire/NoiseSymbolic.lean#L934) | wired, symbolic | 8 + `sym` | kernel | mutant `read1Slip` |
| 12 | Devices that hold the same ops agree. | [`same_ops_same_verdicts`](../engine/core/Termination.lean#L122) | wired, bridged | 2 + `Distinct` | runtime | reversed order, replay |
| 13 | Removing someone takes two confirmations. | [`writes_only_after_two`](../app/community/member/remove/View.lean#L61) | wired | 0 | kernel | first yes writes nothing |
| 14 | Back goes back. | [`back_open`](../app/Proofs.lean#L1311) | wired | 1 | runtime | shipped bug, a mutant |
| 15 | Line wrapping loses only spaces. | [`wrap_keeps`](../engine/renderer/WrapLaws.lean#L134) | wired | 1 | kernel | none yet |

"Review" counts the spec-only definitions, then names the assumptions.
"kernel" means Lean's kernel checks the example; "runtime" means the
example runs native code (real Ed25519, SQLite, rendering) and then
applies the law, so it trusts Lean's compiler too; "conditional" means
one hypothesis stays an assumption. All fifteen use only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

The order puts first what a user is promised about other people
(1–6), then what leaves the device (7–9), then the sessions (10–11),
then agreement (12), then what the user sees and does (13–15).

### 1. Nobody can post as another user

If the store holds no forged signature, the holder of device d's key
signed each valid message from d, as that exact op. The same key holder
also signed the op that put d into its user.

- **Rests on** `Unforgeable`: Ed25519's unforgeability, stated over the
  signatures that one store holds. It is a computational assumption that
  Lean cannot prove. `unscoped_signs_all`
  ([app/community/Proofs.lean:93](../app/community/Proofs.lean#L93))
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
- **Note:** its surface is the largest of the fifteen. See
  [surfaces too big](#surfaces-too-big-to-review).

### 7. A session sends only what its peer may see

A connection replies only with sync messages and with ops of the rooms
that the connection is let into. A local op, such as a session key or a
pending join, is in no room, so it is never sent. (`rooms_trusted`
proves that the connection's rooms are the ones the trust rule allows.)

- **Rests on** the store model.
- **Example:** kernel. `Vacuity.Network.receiveSendable`
  ([tests/vacuity/Network.lean:109](../tests/vacuity/Network.lean#L109)).
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

### 9. Nobody can rename an op

The id of an op read from bytes is the SHA-256 hash of those exact
bytes. With `Codec.encode_decode` (a decoded value has only one
encoding), no peer can change an op and keep its id, unless it finds a
SHA-256 collision.

- **Example:** kernel. `Vacuity.Core.hashNamed`
  ([tests/vacuity/Core.lean:39](../tests/vacuity/Core.lean#L39)).
- **Control:** for `encode_decode`, bytes with one extra byte at the end
  do not decode.

### 10. Session keys stay secret

An active attacker that does not know a session's four secrets (both
static keys and both ephemeral keys) cannot get either side's session
keys, whatever calls it makes to honest nodes. The law is about the
handshake functions that run (`sent1`, `read1`, `read2`, `write2`),
with the cryptography as symbols (Dolev-Yao).

- **Rests on** the symbolic model (`sym`): perfect primitives, no
  computational proof.
- **Example:** kernel. `Vacuity.Session.secretsHeld`
  ([tests/vacuity/Session.lean:29](../tests/vacuity/Session.lean#L29)).
- **Control:** `kk_secret_init_tight`
  ([engine/wire/NoiseSymbolic.lean:654](../engine/wire/NoiseSymbolic.lean#L654)):
  an attacker that knows the initiator's static and ephemeral keys does
  get the keys. So the hypothesis is needed, and the attacker model is
  strong enough to break a weak handshake.

### 11. The dialer knows who answered

Unless the dialed node really answered this request, the dialing node
accepts no reply that an attacker can make. The dialed node's static
key must be secret, and the dialer's static or ephemeral key.

- **Rests on** the symbolic model (`sym`).
- **Example:** kernel. `Vacuity.Session.initiatorAuthenticates`
  ([tests/vacuity/Session.lean:110](../tests/vacuity/Session.lean#L110)).
- **Control:** `read1Slip`, a one-letter slip in the responder's code,
  lets the attacker forge a request (`read1Slip_forged`,
  [engine/wire/NoiseSymbolic.lean:1115](../engine/wire/NoiseSymbolic.lean#L1115),
  a negative control in tests/wiring.txt). `kk_authentic_tight`: with
  the responder's static key leaked, the attacker forges a reply.
- **Not covered:** replay. An old answer can be accepted again.

### 12. Devices that hold the same ops agree

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

### 13. Removing someone takes two confirmations

The removal dialog writes a removal only after the second yes (or a
retry after a refusal that had both), and only for the member that the
user chose. Its surface is four definitions, all the app's own.

- **Example:** kernel. `Vacuity.RendererFlow.secondYes`
  ([tests/vacuity/RendererFlow.lean:12](../tests/vacuity/RendererFlow.lean#L12)).
- **Control:** the first yes writes nothing (an `example` in the same
  file), and cancelling writes nothing (`cancel_writes_nothing`).

### 14. Back goes back

After the user opens a page, Back restores the app state from before,
except for a few fields that belong to the page that closed (its
one-line field, its refusal, its key, its scroll mark, its own sends,
what it presents) and an editor counter.

- **Example:** runtime. `Vacuity.RendererRuntime.backOpen`
  ([tests/vacuity/RendererRuntime.lean:17](../tests/vacuity/RendererRuntime.lean#L17))
  starts a real headless app.
- **Control:** `shipped_back_open_fails`
  ([app/Proofs.lean:1403](../app/Proofs.lean#L1403)). This law caught a
  shipped bug: commit 566e566 lost the switcher's backdrop after gear →
  back. The shipped code is kept as a mutant, and the kernel proves that
  it breaks the law ([what the proofs caught](CAUGHT.md)).
- **Note:** its whole surface is large (224) only because the app's
  state has about 150 fields. The spec-only part is one predicate.

### 15. Line wrapping loses only spaces

When the app wraps a message into lines, the lines keep every character
that is not a space, in the same order.

- **Example:** kernel. `Vacuity.RendererText.wrapping`
  ([tests/vacuity/RendererText.lean:55](../tests/vacuity/RendererText.lean#L55)),
  over Latin, Hebrew and Arabic text.
- **Control:** none yet. A good one, in the kernel: a wrapping that
  drops a letter does not meet the statement. (The same file rejects
  reversed number runs, but that is `numbers_keep_order`'s control.)

## What the fifteen rest on, together

To trust all fifteen, a reviewer reads **42 spec-only definitions**
(32 of them predicates) and **4 assumptions**:

- the **store model** (`Engine.Model.run`, with `DB`, `HeldM` and their
  operations): SQLite's reads and writes answer as the model's tables.
  Tested row for row (tests/engine/Differential.lean), not proven. Laws
  5–8 and 12 depend on it.
- **`Unforgeable`**: Ed25519 unforgeability over one store's
  signatures. Law 1.
- **`Distinct`** (from `CollisionFree`): no SHA-256 collision among the
  ops a node received. Law 12.
- **`sym`**: the symbolic model of the cryptography. Laws 10 and 11.

The generated section below lists the 42 definitions.

## Also considered

All of these are wired and use only the standard axioms. Each is a
good law; each is left out because a top-fifteen law covers it, it
depends on more, or a user cares less.

| Law, in plain words | Lean name | Example | Why not in the fifteen |
|---|---|---|---|
| Every valid message verifies under its author's admitted device key, with no assumption. | `message_authorized` | runtime | 1 says more; this one needs no `Unforgeable`. A good alternative to 1. |
| A removal cuts off the removed user's node. | `removal_cuts_off` | runtime | A consequence of the trust rule's law (5). |
| A removal does not change past verdicts. | `valid_stays` | runtime | Less central to a user than 4. |
| Per connection step, a refused peer gets only the notice. | `removed_gets_only_notice` | runtime | The one-step form of 6, with a smaller surface (7). |
| Every connection step reads its rooms afresh. | `entry_fresh` | runtime | The base of 6. |
| Sync advertises only stored shared ops of the connection's rooms. | `offer_shared` | kernel | The advertising half of 7. |
| A session takes in only ops of its rooms. | `recv_take` | kernel | The receiving half of 7. |
| A frame that does not open changes nothing (any family). | `sealed_unopened` | kernel | The generic form of 8. |
| A decoded value has exactly one encoding. | `Codec.encode_decode` | kernel | Folded into 9. Surface: 4. |
| Judging cannot be hung: a budget read off the tables empties the queue. | `drain_bounded` | runtime | Strong (denial of service); 12 needs the same and shows judging ends. |
| Taking an op in twice is taking it in once. | `ingest_twice` | kernel | Short and clear; less visible to a user. |
| A purge deletes no shared op. | `purge_shared` | runtime | Engine safety; less visible to a user. |
| At rest, the stored verdict is the spec's verdict. | `status_iff_spec` | runtime | The bridge from laws 1–4 to the store. Show it beside them. |
| Devices with the same ops order a channel alike (below the counter cap). | `display_agrees` | runtime | The exception at the cap makes the sentence long. |
| The people list is exactly the present members. | `present_iff` | runtime | Has a mutant control (`shipped_removed_without_removal`). |
| Bidi reordering drops and invents no character. | `visual_perm` | kernel | Surface 55, none spec-only. A good alternative to 15. |
| Picture bytes from a peer decode to 1–2048 pixels a side, or to nothing. | `Image.decode_sized` | kernel | Surface 17, none spec-only. Hostile input. |
| A valid attachment chunk is its file's own slice. | `chunk_is_slice` | conditional | Rests on `NoCollision` and SHA-256's output size. |
| Without a session, a peer can push in only a join request. | `bare_takes_only_join` | runtime | Strong, but its surface is 500. |

For contrast, `Engine.World.Plain.converge` (every member gets every
op, over a web of n nodes) is a *World* law: it runs the node's code,
but in a modelled network with plain frames and sessions that the test
harness opens. tests/Wiring.lean does not count it as wired.

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
   Five of the fifteen depend on it.

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

## Comparator (DRAFT)

Lean v4.35's `lake comparator` checks a solution against a trusted file
of statements. Another stream is checking its exact format, so these
files are drafts:

- [tests/comparator/Challenge.lean](../tests/comparator/Challenge.lean):
  the fifteen statements, word for word, as `Headline.<law>`, each with
  `sorry`. This is the file a judge trusts, with the definitions that
  it names.
- [tests/comparator/Solution.lean](../tests/comparator/Solution.lean):
  generated from the challenge by tests/comparator/solution.py. It
  proves each statement with the law, checks that each statement is the
  law's own (`#same_statement`, which also pairs the matcher that a
  `match` in a statement makes), and prints the axioms.

Neither file is in a lakefile library, so `lake build` never sees a
`sorry`. tests/headline.sh checks both on v4.34, and three controls:
a weakened restatement and a changed `match` must fail
`#same_statement`, and `#headline` must fail on a law that rests on
`sorry`.

Open questions for the format check: whether the two files must be
library modules; whether the challenge may import modules that also
hold the original laws; where the configuration goes. Also: the runtime
examples run native code, which Comparator does not check. Kernel
examples, with a toy `Crypto` as in tests/vacuity/Contracts.lean, would
let laws 2–6, 8, 12 and 14 show satisfiable hypotheses in the kernel.

## Surfaces (generated)

The numbers and lists below are tests/Headline.lean's output, written
by ci/headline.py. Do not edit them by hand. The app's part of each
recommended law is listed whole in
[HEADLINE-SURFACES.md](HEADLINE-SURFACES.md).

<!-- surface:begin: written by ci/headline.py; do not edit -->

### Recommended

| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |
|---|---|---|---:|---:|---:|---:|---:|
| [`no_impersonation`](#communityno_impersonation) | [app/community/Proofs.lean:120](../app/community/Proofs.lean#L120) | propext, Classical.choice, Quot.sound | 318 | 298 | 6 | 1 | 1 |
| [`admission_needs_approval`](#communityadmission_needs_approval) | [app/community/member/invite/Proofs.lean:44](../app/community/member/invite/Proofs.lean#L44) | propext, Classical.choice, Quot.sound | 305 | 297 | 8 | 0 | 0 |
| [`removal_authorized`](#communityremoval_authorized) | [app/community/member/Proofs.lean:50](../app/community/member/Proofs.lean#L50) | propext, Classical.choice, Quot.sound | 305 | 297 | 8 | 0 | 0 |
| [`removed_stays`](#communityremoved_stays) | [app/community/member/remove/Proofs.lean:28](../app/community/member/remove/Proofs.lean#L28) | propext, Classical.choice, Quot.sound | 304 | 297 | 7 | 0 | 0 |
| [`connect_iff`](#communityconnect_iff) | [app/community/Proofs.lean:821](../app/community/Proofs.lean#L821) | propext, Classical.choice, Quot.sound | 349 | 326 | 10 | 1 | 1 |
| [`removal_reaches_session`](#connectionremoval_reaches_session) | [app/Proofs.lean:3088](../app/Proofs.lean#L3088) | propext, Classical.choice, Quot.sound | 613 | 542 | 13 | 24 | 5 |
| [`recv_send`](#enginesyncrecv_send) | [engine/sync/ConnLaws.lean:158](../engine/sync/ConnLaws.lean#L158) | propext, Classical.choice, Quot.sound | 123 | 103 | 3 | 15 | 0 |
| [`sealed_auth`](#connectionsealed_auth) | [app/connection/Proofs.lean:134](../app/connection/Proofs.lean#L134) | propext, Classical.choice, Quot.sound | 318 | 260 | 2 | 23 | 4 |
| [`id_decode`](#engineopid_decode) | [engine/core/Core.lean:93](../engine/core/Core.lean#L93) | propext, Classical.choice, Quot.sound | 35 | 34 | 1 | 0 | 0 |
| [`kk_secret`](#connectionnoisesymbolickk_secret) | [engine/wire/NoiseSymbolic.lean:633](../engine/wire/NoiseSymbolic.lean#L633) | propext, Quot.sound | 29 | 18 | 7 | 1 | 0 |
| [`kk_authentic`](#connectionnoisesymbolickk_authentic) | [engine/wire/NoiseSymbolic.lean:934](../engine/wire/NoiseSymbolic.lean#L934) | propext, Quot.sound | 30 | 18 | 8 | 1 | 0 |
| [`same_ops_same_verdicts`](#enginesame_ops_same_verdicts) | [engine/core/Termination.lean:122](../engine/core/Termination.lean#L122) | propext, Classical.choice, Quot.sound | 68 | 33 | 2 | 3 | 5 |
| [`writes_only_after_two`](#removewrites_only_after_two) | [app/community/member/remove/View.lean:61](../app/community/member/remove/View.lean#L61) | propext, Quot.sound | 4 | 4 | 0 | 0 | 0 |
| [`back_open`](#navlawsback_open) | [app/Proofs.lean:1311](../app/Proofs.lean#L1311) | propext, Classical.choice, Quot.sound | 224 | 223 | 1 | 0 | 0 |
| [`wrap_keeps`](#textwrap_keeps) | [engine/renderer/WrapLaws.lean:134](../engine/renderer/WrapLaws.lean#L134) | propext, Classical.choice, Quot.sound | 37 | 36 | 1 | 0 | 0 |

**Together** these laws name 42 spec-only definitions, and 30 names of the assumptions they take.

<details><summary>The spec-only definitions, together</summary>

- predicates: `Community.Admitted`, `Community.IsAdmin`, `Community.Keyed`, `Community.Live`, `Community.Removed`, `Community.V`, `Connection.LiveIn`, `Connection.MayGo`, `Connection.Noise.Symbolic.Answers`, `Connection.Noise.Symbolic.Clean`, `Connection.Noise.Symbolic.Derivable`, `Connection.Noise.Symbolic.Exposed`, `Connection.Noise.Symbolic.Part`, `Connection.Noise.Symbolic.Reveals`, `Connection.Noise.Symbolic.Sends`, `Connection.Noise.Symbolic.secrets`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Extends`, `Engine.Inv`, `Engine.Reach`, `Engine.Spec`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.Key.lt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReachIn`, `Engine.Sync.Reads`, `Engine.Sync.Sendable`
- types: `Connection.Noise.Symbolic.T`
- definitions: `Community.Fact.admin`, `Community.Fact.admission`, `Community.Fact.approval`, `Community.Fact.message`, `Community.Fact.removal`, `Community.Fact.request`, `Engine.specAt`, `Text.ns`
- instances: `Connection.Noise.Symbolic.instDecidableEqT`
- assumed: `Community.Unforgeable`, `Connection.Noise.Symbolic.sym`, `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.empty`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Distinct`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.instMonadModel`, `Engine.modelStore`

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

Assumed: `Engine.DB`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Connection.removal_reaches_session

Named in the statement: `Community.Fact`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.Keys`, `Connection.MayGo`, `Connection.hooks`, `Connection.instSortKeyFact`, `Engine.Fresh`, `Engine.Id`, `Engine.Op`, `Engine.Sync.Catalog`, `Engine.Sync.Effects`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.Hooks`, `Engine.Sync.Moves`, `Engine.Sync.Node`, `Engine.Sync.Reads`, `Engine.Sync.RetryStore`, `Engine.Sync.Sweep`, `Engine.Sync.Sync`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.instSortKeySum`.

Spec-only, to review: predicates: `Connection.LiveIn`, `Connection.MayGo`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.Key.lt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReachIn`, `Engine.Sync.Reads`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.modelStore`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`), `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Engine.Sync.recv_send

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.recv`, `Engine.Sync.Index`, `Engine.Sync.Sendable`, `Engine.Sync.Step`, `Engine.instMonadModel`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.Sendable`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Connection.sealed_auth

Named in the statement: `Community.Fact`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.Frame.ad`, `Connection.Frame.cid`, `Connection.Keys`, `Connection.instSortKeyFact`, `Connection.openFrame`, `Connection.sessionKeys`, `Engine.Id`, `Engine.Sync.Effects`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.Node`, `Engine.Sync.Node.onFrame`, `Engine.Sync.RetryTicket`, `Engine.Sync.Sync`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.sealedTag`, `Engine.Sync.tagged`, `Engine.instSortKeySum`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instListsHeldMOfSortKey`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Engine.Op.id_decode

Named in the statement: `Engine.Id`, `Engine.Op`, `Engine.Op.decode`, `Engine.sha256`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: none. Bridged: none.

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

Assumed: `Engine.DB`, `Engine.DB.empty`, `Engine.Distinct`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`), `Engine.stepS` (by `Engine.run_step`).

#### Remove.writes_only_after_two

Named in the statement: `Engine.Id`, `Remove.Ev`, `Remove.Step`, `Remove.step`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### NavLaws.back_open

Named in the statement: `App.PageId`, `App.PageIn`, `App.Presentation.Entry`, `App.Presentation.capacity`, `App.PresentationCandidate`, `App.St`, `App.backSt`, `App.openSt`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: none. Bridged: none.

#### Text.wrap_keeps

Named in the statement: `Font.Font`, `Text.ns`, `Text.wrapL`.

Spec-only, to review: definitions: `Text.ns`.

Assumed: none. Bridged: none.

### Also considered

| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |
|---|---|---|---:|---:|---:|---:|---:|
| [`message_authorized`](#communitymessage_authorized) | [app/community/channel/message/Proofs.lean:64](../app/community/channel/message/Proofs.lean#L64) | propext, Classical.choice, Quot.sound | 316 | 298 | 6 | 0 | 1 |
| [`removal_cuts_off`](#communityremoval_cuts_off) | [app/community/Proofs.lean:918](../app/community/Proofs.lean#L918) | propext, Classical.choice, Quot.sound | 348 | 326 | 9 | 1 | 1 |
| [`valid_stays`](#communityvalid_stays) | [app/community/Family.lean:1280](../app/community/Family.lean#L1280) | propext, Classical.choice, Quot.sound | 302 | 297 | 5 | 0 | 0 |
| [`removed_gets_only_notice`](#connectionremoved_gets_only_notice) | [app/Proofs.lean:210](../app/Proofs.lean#L210) | propext, Classical.choice, Quot.sound | 286 | 252 | 7 | 16 | 1 |
| [`entry_fresh`](#enginesyncentry_fresh) | [engine/wire/EgressLaws.lean:964](../engine/wire/EgressLaws.lean#L964) | propext, Classical.choice, Quot.sound | 275 | 220 | 10 | 21 | 4 |
| [`offer_shared`](#enginesyncoffer_shared) | [engine/sync/SecrecyLaws.lean:62](../engine/sync/SecrecyLaws.lean#L62) | propext, Classical.choice, Quot.sound | 95 | 74 | 1 | 18 | 0 |
| [`recv_take`](#enginesyncrecv_take) | [engine/sync/ConnLaws.lean:129](../engine/sync/ConnLaws.lean#L129) | propext, Classical.choice, Quot.sound | 123 | 103 | 3 | 15 | 0 |
| [`sealed_unopened`](#enginesyncsealed_unopened) | [engine/wire/NodeLaws.lean:70](../engine/wire/NodeLaws.lean#L70) | propext, Classical.choice, Quot.sound | 234 | 188 | 2 | 20 | 4 |
| [`encode_decode`](#enginecodecencode_decode) | [engine/core/Codec.lean:775](../engine/core/Codec.lean#L775) | propext | 4 | 3 | 1 | 0 | 0 |
| [`drain_bounded`](#enginedrain_bounded) | [engine/core/Budget.lean:167](../engine/core/Budget.lean#L167) | propext, Classical.choice, Quot.sound | 71 | 32 | 2 | 4 | 5 |
| [`ingest_twice`](#engineingest_twice) | [engine/core/IdemLaws.lean:50](../engine/core/IdemLaws.lean#L50) | propext, Classical.choice, Quot.sound | 51 | 32 | 1 | 15 | 0 |
| [`purge_shared`](#enginepurge_shared) | [engine/core/Purge.lean:578](../engine/core/Purge.lean#L578) | propext, Classical.choice, Quot.sound | 47 | 32 | 1 | 1 | 1 |
| [`status_iff_spec`](#enginestatus_iff_spec) | [engine/core/Proofs.lean:484](../engine/core/Proofs.lean#L484) | propext, Classical.choice, Quot.sound | 42 | 37 | 4 | 1 | 0 |
| [`display_agrees`](#communitydisplay_agrees) | [app/community/channel/message/Proofs.lean:193](../app/community/channel/message/Proofs.lean#L193) | propext, Classical.choice, Quot.sound | 314 | 306 | 8 | 0 | 0 |
| [`present_iff`](#peoplelawspresent_iff) | [app/community/Screen.lean:439](../app/community/Screen.lean#L439) | propext, Classical.choice, Quot.sound | 351 | 328 | 10 | 1 | 1 |
| [`visual_perm`](#textvisual_perm) | [engine/renderer/TextLaws.lean:21](../engine/renderer/TextLaws.lean#L21) | propext, Quot.sound | 55 | 55 | 0 | 0 | 0 |
| [`decode_sized`](#imagedecode_sized) | [engine/renderer/ImageLaws.lean:13](../engine/renderer/ImageLaws.lean#L13) | propext, Classical.choice, Quot.sound | 17 | 17 | 0 | 0 | 0 |
| [`chunk_is_slice`](#communitychunk_is_slice) | [app/community/channel/message/attachment/chunk/Proofs.lean:51](../app/community/channel/message/attachment/chunk/Proofs.lean#L51) | propext, Classical.choice, Quot.sound | 181 | 171 | 3 | 1 | 0 |
| [`bare_takes_only_join`](#connectionbare_takes_only_join) | [app/Proofs.lean:610](../app/Proofs.lean#L610) | propext, Classical.choice, Quot.sound | 500 | 469 | 2 | 17 | 0 |

**Together** these laws name 34 spec-only definitions, and 28 names of the assumptions they take.

<details><summary>The spec-only definitions, together</summary>

- predicates: `Community.Admitted`, `Community.Listed`, `Community.Live`, `Community.Posted`, `Community.Removed`, `Community.V`, `Connection.LiveIn`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Extends`, `Engine.Inv`, `Engine.Reach`, `Engine.Spec`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.FramesOk`, `Engine.Sync.Key.lt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReachIn`, `Engine.Sync.ReadOnly`, `Engine.Sync.Reads`, `Engine.Sync.Sent`, `Engine.Sync.Takeable`
- definitions: `Community.Fact.admission`, `Community.Fact.chunk`, `Community.Fact.message`, `Community.Fact.received`, `Community.Fact.removal`, `Connection.Fact.opened`, `Engine.specAt`, `Merkle.slices`
- assumed: `Community.ChunkSound`, `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.empty`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Distinct`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.instMonadModel`, `Engine.modelStore`

</details>

#### Community.message_authorized

Named in the statement: `Community.Body`, `Community.Body.post`, `Community.Crypto`, `Community.Fact.admission`, `Community.Fact.message`, `Community.Key`, `Community.V`, `Community.instCodecBody`, `Community.signed`, `Engine.Codec.decode`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.message`, `Engine.specAt`.

Assumed: none. Bridged: `Community.signed` (by `Community.signed_eq`).

#### Community.removal_cuts_off

Named in the statement: `Community.Admitted`, `Community.Crypto`, `Community.Fact`, `Community.Key`, `Community.Removed`, `Community.allowPeer`, `Community.family`, `Community.instSortKeyFact`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Engine.View.eval`.

Spec-only, to review: predicates: `Community.Admitted`, `Community.Removed`, `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.removal`, `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Community.valid_stays

Named in the statement: `Community.Crypto`, `Community.Fact`, `Community.V`, `Engine.Extends`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Extends`, `Engine.Spec`; definitions: `Engine.specAt`.

Assumed: none. Bridged: none.

#### Connection.removed_gets_only_notice

Named in the statement: `Community.Fact`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.LiveIn`, `Connection.NoticeOnly`, `Connection.Refused`, `Connection.instSortKeyFact`, `Connection.roomsV`, `Engine.DB`, `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.carry`, `Engine.Sync.Conn.filedGive`, `Engine.Sync.Conn.open`, `Engine.Sync.Conn.recv`, `Engine.Sync.Conn.tickGive`, `Engine.Sync.Index`, `Engine.Sync.Room`, `Engine.Sync.Step`, `Engine.Sync.isWire`, `Engine.View.eval`, `Engine.instMonadModel`, `Engine.instSortKeySum`, `Engine.modelStore`.

Spec-only, to review: predicates: `Connection.LiveIn`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.ReachIn`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.eval`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Engine.Sync.entry_fresh

Named in the statement: `Engine.Sync.Effects`, `Engine.Sync.Entry`, `Engine.Sync.FramesOk`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.Moves`, `Engine.Sync.Node`, `Engine.Sync.ReadOnly`, `Engine.Sync.Sync`, `Engine.Sync.instMonadHeldM`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.FramesOk`, `Engine.Sync.Key.lt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReadOnly`, `Engine.Sync.Reads`, `Engine.Sync.Sent`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Engine.Sync.offer_shared

Named in the statement: `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.filed`, `Engine.Sync.Conn.walk`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.Msg.op`, `Engine.Sync.Step`, `Engine.Sync.holdsOf`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.has`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.lift`, `Engine.modelStore`. Bridged: none.

#### Engine.Sync.recv_take

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.recv`, `Engine.Sync.Index`, `Engine.Sync.Step`, `Engine.Sync.Takeable`, `Engine.instMonadModel`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.Takeable`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Engine.Sync.sealed_unopened

Named in the statement: `Engine.Id`, `Engine.Sync.Effects`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.Node`, `Engine.Sync.Node.onFrame`, `Engine.Sync.RetryTicket`, `Engine.Sync.Sync`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Engine.Codec.encode_decode

Named in the statement: `Engine.Codec`, `Engine.Codec.decode`, `Engine.Codec.encode`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: none. Bridged: none.

#### Engine.drain_bounded

Named in the statement: `Engine.DB`, `Engine.Distinct`, `Engine.Family`, `Engine.Id`, `Engine.Op`, `Engine.Reach`, `Engine.budget`, `Engine.drainS`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Reach`.

Assumed: `Engine.DB`, `Engine.DB.empty`, `Engine.Distinct`, `Engine.budget`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`), `Engine.stepS` (by `Engine.run_step`).

#### Engine.ingest_twice

Named in the statement: `Engine.DB`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.ingest`, `Engine.instMonadModel`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Engine.purge_shared

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Op`, `Engine.purgeS`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`. Bridged: `Engine.purgeS` (by `Engine.run_purge`).

#### Engine.status_iff_spec

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Id`, `Engine.Inv`, `Engine.Spec`, `Engine.Verdict`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: none.

#### Community.display_agrees

Named in the statement: `Community.Crypto`, `Community.Listed`, `Community.Posted`, `Community.countCap`, `Engine.Id`, `Engine.Op`, `Engine.Pos.cmp`.

Spec-only, to review: predicates: `Community.Listed`, `Community.Posted`, `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.message`, `Community.Fact.received`, `Engine.specAt`.

Assumed: none. Bridged: none.

#### PeopleLaws.present_iff

Named in the statement: `Community.Admitted`, `Community.Crypto`, `Community.Fact`, `Community.Key`, `Community.Live`, `Community.family`, `Community.instSortKeyFact`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Engine.View.eval`, `Kinds.Profile.present`.

Spec-only, to review: predicates: `Community.Admitted`, `Community.Live`, `Community.Removed`, `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.removal`, `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Text.visual_perm

Named in the statement: `Text.visual`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Image.decode_sized

Named in the statement: `Image.Src`, `Image.decode`, `Pic.maxSide`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Community.chunk_is_slice

Named in the statement: `Community.Body`, `Community.Body.chunk`, `Community.ChunkSound`, `Community.Crypto`, `Community.Fact`, `Community.Fact.chunk`, `Community.check`, `Engine.Id`, `Engine.Op`, `Engine.sha256`, `Merkle.B`, `Merkle.fileRoot`, `Merkle.proof`, `Merkle.slices`.

Spec-only, to review: predicates: `Engine.Codec.At`; definitions: `Community.Fact.chunk`, `Merkle.slices`.

Assumed: `Community.ChunkSound`. Bridged: none.

#### Connection.bare_takes_only_join

Named in the statement: `Community.Body`, `Community.Body.request`, `Community.Crypto`, `Community.Fact`, `Community.instCodecBody`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.Fact.opened`, `Connection.Keys`, `Connection.instSortKeyFact`, `Connection.node`, `Connection.opened.all`, `Connection.react`, `Engine.Codec.decode`, `Engine.DB`, `Engine.Family.room`, `Engine.Fresh`, `Engine.Id`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Op.bytes`, `Engine.Pos`, `Engine.Rel.query`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.instMonadModel`, `Engine.instSortKeySum`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`; definitions: `Connection.Fact.opened`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

### For contrast: a World law

| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |
|---|---|---|---:|---:|---:|---:|---:|
| [`converge`](#engineworldplainconverge) | [engine/world/Plain.lean:203](../engine/world/Plain.lean#L203) | propext, Classical.choice, Quot.sound | 300 | 222 | 33 | 21 | 4 |

#### Engine.World.Plain.converge

Named in the statement: `Engine.Id`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.World.Diam`, `Engine.World.Edge`, `Engine.World.Exec`, `Engine.World.Exec.world`, `Engine.World.Holds`, `Engine.World.Net`, `Engine.World.Net.Calm`, `Engine.World.Plain`, `Engine.World.Plain.setup`, `Engine.World.World`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.World.Diam`, `Engine.World.Edge`, `Engine.World.Holds`, `Engine.World.Legal`, `Engine.World.Net.Calm`, `Engine.World.Net.Live`, `Engine.World.Net.Up`, `Engine.World.Path`; types: `Engine.Sync.Setup`, `Engine.Sync.Who`, `Engine.World.Act`, `Engine.World.Exec`, `Engine.World.Net`, `Engine.World.Packet`, `Engine.World.Plain`, `Engine.World.Setup`, `Engine.World.World`; definitions: `Engine.Sync.Node.connect`, `Engine.Sync.Setup.sync`, `Engine.Sync.plainOpen`, `Engine.Sync.plainSeal`, `Engine.World.Exec.world`, `Engine.World.Plain.setup`, `Engine.World.Plain.two`, `Engine.World.Setup.at?`, `Engine.World.World.enter`, `Engine.World.World.step`, `Engine.World.packets`, `Engine.World.plainPeek`, `Engine.World.upd`, `Engine.World.worlds`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

<!-- surface:end -->
