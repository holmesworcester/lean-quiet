# Built during the hackathon

Lean Quiet is an entry in the Vibecheck hackathon ([rules](VIBECHECK-RULES.md)).
The hackathon started on Saturday 2026-10-31 at 10:00 PDT. At that time,
main was at [`89914bea`](https://github.com/holmesworcester/lean-quiet/commit/89914bea346ddf93d9a065a2e8bef0c79ed47797). This page calls that commit **the base**. The
judges score only the work done after the base. This page says what
changed, and a script computes its numbers from git.

## What existed at the base

The app was not new at the base. It built for iOS, Android, Linux and
Apple Silicon macOS. It did end-to-end encrypted, peer-to-peer chat with
emojis, reactions and photos, over TCP and Noise, with SQLite storage.
Lean drew the app's screens, with Noto fonts and mixed left-to-right
and right-to-left text. Its README listed 1016 laws: 787 were about the code
that runs, and 20 more laws were negative controls. Of its 85 promises
to users, 40 were proven over running code (✅). Please compare the work
below with that.

## The numbers

[ci/hackathon.py](../ci/hackathon.py) reads the base and the head with git.
It needs no build. It takes the law counts from the README's lead line.
[ci/proof-links.py](../ci/proof-links.py) writes that line from
[tests/Wiring.lean](../tests/Wiring.lean), and the gate checks it against
the code (`mise run readme:links`).

<!-- hackathon:begin -->
<!-- hackathon:end -->

- A law is **about running code** when every definition its statement
  names runs from the app's `main` or the node's runner, or is proven
  equal to code that does. The README's "Not yet about running code"
  section lists the rest, with what each one lacks.
- A law **in a World** runs the node's own code over a modelled network.
- A **negative control** is a law that proves a mutant of the code breaks
  a law. It shows that the law can fail.
- The README's "Not yet about running code" section lists each law that
  is not yet about running code, with what it lacks. Many of those added
  since the base belong to the fair-service and liveness work (theme 3):
  they are stated over run harnesses, such as `Execution`, `RoundRun`,
  `Prioritized` and `Ingress`, which the check counts as models.
- The numbers count main as it is. So they include the six commits that
  were written before the start (see "Work from before the start").

**Refresh before submission.** Run `python3 ci/hackathon.py --refresh`
(or `mise run hackathon:refresh`) at main's head. It writes the block
above, commits this file alone, and then runs the script's self-test
and `--check`. `mise run hackathon:check` fails when anything but this
file has changed since the commit that the block names.

## What changed

1. **Vacuity audit: a concrete input for every linked law.** A law with
   hypotheses that can never hold together proves nothing. For each
   declaration that the README links, a check builds a concrete input
   that meets every hypothesis and applies the law to it. Lean's kernel
   checks most of these. The rest run the native code and check the
   result. Some stay conditional on a named assumption, such as Ed25519
   unforgeability, which a finite check cannot prove. The audit started at [`74dea236`](https://github.com/holmesworcester/lean-quiet/commit/74dea2361edfe17ea860812302b6617f271e6fd5). By [`b8387523`](https://github.com/holmesworcester/lean-quiet/commit/b83875239ee0574e43acdb09b2be40b888c26394), each of the
   511 declarations linked then had an entry: a witness, a conditional
   check that names its open assumption, or a counterexample. It found
   two premises that the native crypto did not meet (theme 2). See [tests/vacuity/](../tests/vacuity),
   [ci/vacuity.py](../ci/vacuity.py) and the README's "Vacuity check
   reports". `mise run test:vacuity` runs in the gate. The block above
   gives the coverage at the head and names the laws still pending.

2. **Crypto contracts that the code meets, and sized keys.** The audit
   showed that `Seal.Good` and Noise's `Suite.Good` were false of the
   native crypto. For example, a key of the wrong size sealed to empty
   bytes ([`5c1d4036`](https://github.com/holmesworcester/lean-quiet/commit/5c1d40361e707a8006442bf939ccef7572fc0c66)). So the laws that assumed them could not apply
   to the running code. The contracts now cover only the sizes that the
   crates support ([`0b59f14c`](https://github.com/holmesworcester/lean-quiet/commit/0b59f14c765ce14269ca7042d36b3c46a79ea1a0), [`e48edb27`](https://github.com/holmesworcester/lean-quiet/commit/e48edb27f9057ac3cb6df3dc87e220ce430651ed)). Native seal errors now
   reach the caller ([`208d4199`](https://github.com/holmesworcester/lean-quiet/commit/208d4199f7b3ddce8d9bd40235901b73361a7578)), and the AEAD bounds respect the
   cipher's counter limit ([`cd4d7c84`](https://github.com/holmesworcester/lean-quiet/commit/cd4d7c84e15ec89dc2f42e54072b4a4f7b7d96a8)). Then keys and nonces became
   sized types (`Bytes 32`, `Bytes 24`), so no law needs a size premise
   ([`67cfc08a`](https://github.com/holmesworcester/lean-quiet/commit/67cfc08ab3e1590a3fe3753d644639159479e17d), merged in [`e770ab94`](https://github.com/holmesworcester/lean-quiet/commit/e770ab94f6ca7eb973097e699787f87bb9127347)). What the proofs trust about
   the crypto crates is one file of named premises, never axioms:
   [engine/core/Trust.lean](../engine/core/Trust.lean).
   [tests/vacuity/CryptoTrust.lean](../tests/vacuity/CryptoTrust.lean)
   checks that the native crates meet each premise and that a broken
   model does not. The same pattern now covers SQLite
   ([engine/core/StoreTrust.lean](../engine/core/StoreTrust.lean),
   [`728c5cb0`](https://github.com/holmesworcester/lean-quiet/commit/728c5cb04986a3d44d258b3275e6c2c15e90339f)), and the wiring check fails on an `@[extern]` without a
   stated contract ([`755254b2`](https://github.com/holmesworcester/lean-quiet/commit/755254b28c2be2849457432b90158ea3c1048713)).

3. **Fair service, with local work first.** The node's loop now serves
   local writes, network events and ticks fairly ([`1b334291`](https://github.com/holmesworcester/lean-quiet/commit/1b3342917a3d2ea8e7aa4111382623f2fd11231d)), and
   gives local work priority with a bounded share for sync
   ([`d90dc7c5`](https://github.com/holmesworcester/lean-quiet/commit/d90dc7c51e0972acd76500ef02d8daabfa62ed71), [`00baa2c5`](https://github.com/holmesworcester/lean-quiet/commit/00baa2c5c2c12c08ca7c962337e95be89cef8b6b), [`60de8ab6`](https://github.com/holmesworcester/lean-quiet/commit/60de8ab6ea6b43f00a08d9291962b9fe3f2b2756)). The laws say that three of
   every four polls prefer local writes (`Priority.local_share`). A
   waiting local write is chosen within 2 polls per place in its queue,
   and a network event within 4 per place, even while local writes keep
   coming (`Priority.write_within`, `Priority.event_within`). The write
   bound still holds with per-peer fairness for inbound frames
   (`Prioritized.write_within`). The laws are in
   [engine/wire/PriorityLaws.lean](../engine/wire/PriorityLaws.lean) and
   [engine/wire/IngressPriorityLaws.lean](../engine/wire/IngressPriorityLaws.lean).
   For a join, a successful run of the node's own code, with the real
   connection hooks and native crypto, continues with an infinite fair
   run (`successful_fair_extension`, `Execution.fairRun_fair`, World laws;
   [`a785a9ee`](https://github.com/holmesworcester/lean-quiet/commit/a785a9eed18654aa7dc4d113f81e8afbae6fcbd1), [`5aadd831`](https://github.com/holmesworcester/lean-quiet/commit/5aadd831411c0b6a2236dffd64ef88c0f72303bc)). `mise run test:fairness` runs the real
   encrypted runner over TCP, with negative controls. **Limits:** on main,
   the check counts the priority laws as not yet about running code,
   because they are stated over run harnesses. Not proven yet:
   convergence for every fair run of the app, and bounds from a commit to
   the screen. See [docs/EXECUTION-PROGRESS.md](EXECUTION-PROGRESS.md) and
   [docs/BOOTSTRAP-LIVENESS.md](BOOTSTRAP-LIVENESS.md).

4. **Forensics fixes: laws restated over the code that runs.** An audit
   of main at [`0958e672`](https://github.com/holmesworcester/lean-quiet/commit/0958e672c56cf55cc06b9fbd593bad0ec8e8db61) looked for premises that the running code
   cannot meet, and for laws weaker than their README rows. The fixes
   ([`3dd5a416`](https://github.com/holmesworcester/lean-quiet/commit/3dd5a4165622d54889ac65258599deb55ff28fce), [`316ded1c`](https://github.com/holmesworcester/lean-quiet/commit/316ded1c9142abeb56cab64151fc0e896f51231e), merged in [`b4d103a9`](https://github.com/holmesworcester/lean-quiet/commit/b4d103a9f9a342d3f2d4f5b0fca89f1722b5b2af)):
   - `Unforgeable` covered every signature that could exist. So it could
     hold only if every message counted as signed, and the laws that used
     it said nothing about who signed. It now covers the signatures in
     the store (`unscoped_signs_all` is the old form's negative control).
   - The attachment laws assumed no second preimage of SHA-256, which is
     false. They now assume no collision among the hashes at hand
     (`Merkle.NoCollision`), and a test decides that on real SHA-256.
   - The desktop layout laws are now about `zoomLayout` at every density,
     which the driver paints, not about `layout` at one density.
   - `mutual_removal` now derives both removals from signed ops instead
     of assuming them, weak vacuity witnesses got real conclusions, and
     unused premises went.
   - The bootstrap model went, with its laws: nothing that runs imported
     it ([`147a0d2e`](https://github.com/holmesworcester/lean-quiet/commit/147a0d2edcd0202b25e2b450fb7428769de91ba0); [docs/NET.md](NET.md)).

5. **Removal reaches every live session, and ended sessions leave no
   keys.** In every entry point of the node, each connection step reads
   its rooms afresh (`entry_fresh`, [`6628b514`](https://github.com/holmesworcester/lean-quiet/commit/6628b51453aae0d301765e0f69fe33cc0bca9115)). So the README row "A
   removal ends a live session's sync" went from 🟡 at the base to ✅.
   Each frame sealed for a removed member's session carries, of that
   community, only sync messages and the removal with the ops it
   requires, and then the session closes (`removal_reaches_session`,
   [`5970dab1`](https://github.com/holmesworcester/lean-quiet/commit/5970dab1db6d3991b2ea0fa54a3fd34587636f84)). The README row "No packet goes to a removed member but
   the notice of its removal" stays 🟡: the bare handshake replies are
   proven per step only. A retiring session now
   reads to the peer's end, so the removed peer gets its notice
   ([`8a8a0191`](https://github.com/holmesworcester/lean-quiet/commit/8a8a01912c16ac2660a50b72a21e147d5e2add6f)). Every ended session's keys are purged, also after a
   crash (`close_forgets`, `purge_forgets`, `forget_stays`,
   `retired_complete`; [`50176d41`](https://github.com/holmesworcester/lean-quiet/commit/50176d41e05869009aa6bac6f6a2dde21f2e8bf5)). A law found the crash case: see
   [docs/CAUGHT.md](CAUGHT.md). The README row "A closed session's keys
   cannot be recovered" stays 🟡: it assumes that a deleted row leaves
   no bytes on disk, and a phone backup is not covered. Saving a checkpoint now deletes the older
   ones, which held invite seeds and drafts ([`50176d41`](https://github.com/holmesworcester/lean-quiet/commit/50176d41e05869009aa6bac6f6a2dde21f2e8bf5)). On SQLite, a
   purge runs as the model's purge, under SQLite's stated contract
   (`purge_as_model`, [`f5312c9a`](https://github.com/holmesworcester/lean-quiet/commit/f5312c9a47bdb0b4b91ba74a54d643e6f904b09e)). The
   law that the running purge is the model's purge (`run_purge`) was
   written before the start (see below). The test that deleted rows leave
   no bytes on disk (`mise run test:engine`) is also older than the base.

6. **The glyph memo is proven.** At the base, the glyph cache was an
   `unsafe` seam behind `implemented_by`, and its equality with the
   raster was tested, not proven. Now each font source keeps a lazy table
   of thunks, and `@[csimp]` `bitmap_eq_fast` proves that what the
   compiler runs equals rastering the glyph, with no `unsafe` and no
   `implemented_by` (`Table.get_eq`; `shifted_not_exact` is its negative
   control). See
   [engine/renderer/Ttf/Memo.lean](../engine/renderer/Ttf/Memo.lean) and
   [docs/NOTO.md](NOTO.md) ([`2e428a96`](https://github.com/holmesworcester/lean-quiet/commit/2e428a96374a56f928dde66d028f7ad2b2688f5e), [`33c0ffe3`](https://github.com/holmesworcester/lean-quiet/commit/33c0ffe3e5eb947b942c2fb362fe30e91f48a752), [`5a8dcbaf`](https://github.com/holmesworcester/lean-quiet/commit/5a8dcbafe7b7839e5aee748bf0fea9bb156a6146)).
   **Limit:** the old cache had a 4 MiB bound. The memo keeps each glyph
   until the app rebuilds its fonts (on suspend and on a density change),
   so a memory bound is "not yet" in the README.

7. **UI work on iOS, Android and desktop.**
   - iOS: UIKit owns conversation scrolling and deceleration
     ([`841954f1`](https://github.com/holmesworcester/lean-quiet/commit/841954f1839df1747d58a6ece49af9f0c1514900)), a fling keeps its speed ([`8fe0bff2`](https://github.com/holmesworcester/lean-quiet/commit/8fe0bff2e468ac8db493df886c4f55c70a19bcf5)), and press
     timing uses UIKit's clock, tested with real short touches
     ([`c59090b2`](https://github.com/holmesworcester/lean-quiet/commit/c59090b255f5e41ed6056a9ce632dfd22d55845c)).
   - Android: the activity and keyboard survive recreation
     ([`1bb5a53f`](https://github.com/holmesworcester/lean-quiet/commit/1bb5a53f9f1c0c3dc6f3a38b2de9c6e7f8309454)), editor actions go through admission ([`8bd282c7`](https://github.com/holmesworcester/lean-quiet/commit/8bd282c7beb064e43260522b83ff897a752083e3)),
     and a retired owner cancels its own photo request ([`2ee6e4a3`](https://github.com/holmesworcester/lean-quiet/commit/2ee6e4a38b132830c02c3fefa774a89e04019907)).
   - Desktop: `leanquiet://` invite links reach the Linux and macOS apps
     ([`92e6ee1e`](https://github.com/holmesworcester/lean-quiet/commit/92e6ee1e408c2028f977c08df1a2449111ce15a6)), the scrollbar is placed by message rank, with laws
     ([`519dd957`](https://github.com/holmesworcester/lean-quiet/commit/519dd9578cbd0b42c30e4b0ab1f744b5e03e23f5)), and a new native Windows shell runs the same Lean app
     ([`00dfdfb0`](https://github.com/holmesworcester/lean-quiet/commit/00dfdfb04cc19db3f3c4595ee08832492467b312); [platforms/windows](../platforms/windows/README.md)).
   - Shared screens: the phones' community switcher and the Get started
     screen follow Quiet's design ([`566e5664`](https://github.com/holmesworcester/lean-quiet/commit/566e56647ac37f165fb26e11024c5a39f2176621), [`4c5dd94d`](https://github.com/holmesworcester/lean-quiet/commit/4c5dd94d0692f9f4197bac3264771058a328d920)). The law "Back goes
     back" caught a bug in the switcher change ([`e62ab114`](https://github.com/holmesworcester/lean-quiet/commit/e62ab114d564234f923b604a76bb67696f4eec9a);
     [docs/CAUGHT.md](CAUGHT.md)).

**Also on main.** The op tree: each op type is a folder with its
validator, and [ci/layout.py](../ci/layout.py) checks the layout
([`930b39f3`](https://github.com/holmesworcester/lean-quiet/commit/930b39f35b729c5da31f70788ae801424a88a7d9), [`04322c45`](https://github.com/holmesworcester/lean-quiet/commit/04322c45467731480d6ba5faadc0a8939e3c5ef6), [`db9eaf6f`](https://github.com/holmesworcester/lean-quiet/commit/db9eaf6fe4f2ca4c0f462d0b824de0d806f674dc)). An n-node World: convergence
over any network of nodes, given a delivery bound per edge; the World
count above includes it ([`6410107b`](https://github.com/holmesworcester/lean-quiet/commit/6410107b217621928fddac82d4a649f108fa6875), [`8c8375b1`](https://github.com/holmesworcester/lean-quiet/commit/8c8375b1413bf652eceffbf3ba754892182a7d12)). One approval admits a member;
invitation thresholds are gone ([`4e23e2f6`](https://github.com/holmesworcester/lean-quiet/commit/4e23e2f664689f65a9b5c44c0803753845523f2d)). A fast gate before every
push to main, and landing through `ci/land.sh` ([`5a49489d`](https://github.com/holmesworcester/lean-quiet/commit/5a49489d0f400f810d79bddd75ce2129c603515c),
[`a105a8ce`](https://github.com/holmesworcester/lean-quiet/commit/a105a8ce78eaa5a16dc8e81f1264a5422b80050e)). Invite links through a join page, and Linux and macOS
release scripts ([`0cdc5982`](https://github.com/holmesworcester/lean-quiet/commit/0cdc5982b518d0202cf90a38277e9fb53f534f05), [`fb66dee0`](https://github.com/holmesworcester/lean-quiet/commit/fb66dee0c5139cbbee8b1344a3e8b023e21b8d1b); [docs/RELEASE.md](RELEASE.md)).

## Work from before the start

- Six commits on main were authored on 2026-10-28, before the start:
  the purge bridge (branch `fd/purge-bridge`, `run_purge`). They were
  merged during the hackathon, in [`94e900da`](https://github.com/holmesworcester/lean-quiet/commit/94e900da68dae84aecbd155f4bae49f1e32527a2). The block above lists
  them. On their branch, they moved 23 laws to "about running code"
  ([`a0e735dd`](https://github.com/holmesworcester/lean-quiet/commit/a0e735dd03e9d9709c244e59ec4477c95ca9f375)). The numbers count main as it is, so they include this
  work.
- One entry in "Caught by a law" in [docs/CAUGHT.md](CAUGHT.md), the
  replayed handshake, was found on 2026-10-28. Its fix is not on main.
- Everything at the base: see "What existed at the base".

## In progress (not on main)

Nothing in this section is on main. Each item names its branch, and it
moves up to "What changed" when it lands.

- `vibecheck/toolchain`: Lean v4.35.0, with the phone and desktop
  runtimes built from v4.35.0 sources.
- `vibecheck/theorems`: the headline laws (`docs/HEADLINE.md` on the
  branch), each with its spec surface and axioms, and a Comparator
  challenge for them, with a weakened challenge as a negative control.
- `vibecheck/make`: a Makefile with `install` and `run` targets for
  Linux, which the rules require, with pinned published assets and a
  clean-room test in Docker.
- `vibecheck/mac`: `make install && make run` on macOS.
- `vibecheck/demo`: a two-window demo.
- `vibecheck/claims`: fixes to README claims, the SQLite contract, and
  SQLite's `synchronous=FULL`.
- `a3/no-models` (pushed to origin): a ratchet against laws over models.
  `tests/wiring-models.txt` lists the laws that the check counts as over
  a model. The wiring check fails on any other model law, and the list
  can only get shorter. On the branch, many model laws are restated over
  the running code or deleted, and "proof steps" (lemmas that a law about
  running code uses) are counted apart. At its tip [`5c1da634`](https://github.com/holmesworcester/lean-quiet/commit/5c1da634dc5298c80d30673a99d0e4a2f8093e69), its
  README's lead line reads: 1159 of 1288 laws about running code, 35 in a
  World, 94 not yet, 59 proof steps and 25 negative controls.

<!--
For the lead: when a3/no-models lands, update theme 3's "Limits" (the
priority laws may then count as about running code) and the note on
harness laws under "The numbers".

When vibecheck/toolchain, vibecheck/theorems and
vibecheck/make (and vibecheck/mac) land, check these sentences against
main, then move them up as theme 8 and drop those branches from the list:

8. **Lean 4.35, Comparator, and make.** The toolchain is Lean v4.35.0
   (`lean-toolchain`), and the phone and desktop runtimes are built from
   v4.35.0 sources. docs/HEADLINE.md picks the headline laws, with each
   law's spec surface and axioms (tests/Headline.lean), and Comparator
   accepts each law against its stated challenge and rejects a weakened
   one (`mise run test:headline`). `make install && make run` works on
   Linux (and macOS), tested from a clean clone in Docker
   (`mise run make:clean-room`).
-->
