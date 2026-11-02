# Built during the hackathon

Lean Quiet is an entry in the Vibecheck hackathon
([rules](VIBECHECK-RULES.md)). The hackathon started on Saturday
2026-10-31 at 10:00 PDT. At that time, main was at [`89914bea`][89914bea].
This page calls that commit **the base**. The judges score only the work
done after the base. This page says what changed, and a script computes
its numbers from git.

## What existed at the base

The app was not new at the base. It built for iOS, Android, Linux and
Apple Silicon macOS. It did end-to-end encrypted, peer-to-peer chat with
emojis, reactions and photos, over TCP and Noise, with SQLite storage.
Lean drew the app's screens, with Noto fonts and mixed left-to-right and
right-to-left text. Its README listed 1016 laws: 787 were about the code
that runs, and 20 more laws were negative controls. Of its 85 promises to
users, 40 were proven over running code (✅). Please compare the work below
with that.

## The numbers

[ci/hackathon.py](../ci/hackathon.py) reads the base and the head with
git. It needs no build. It takes the law counts from the README's lead
line. [ci/proof-links.py](../ci/proof-links.py) writes that line from
[tests/Wiring.lean](../tests/Wiring.lean), and the gate checks it against
the code (`mise run readme:links`).

Submissions closed on 2026-11-01 at 16:30 PDT. The submitted commit is
the tag `vibecheck-submission` ([`5825ebc3`][5825ebc3]). At that tag the
script gives 1,075 of 1,409 laws about running code, 299 not yet, and 25
negative controls (`python3 ci/hackathon.py --head vibecheck-submission`).
The block below is computed at a later head, so it also counts the work
listed under "Changed after the submission".

<!-- hackathon:begin -->
Computed by `ci/hackathon.py` from git alone, at [`9fd07c18c164`](https://github.com/holmesworcester/lean-quiet/commit/9fd07c18c1643404f08d7279e520f3c157a876dd) (committed 2026-11-01 18:46 -0800), against the base [`89914bea346d`](https://github.com/holmesworcester/lean-quiet/commit/89914bea346ddf93d9a065a2e8bef0c79ed47797) (main at the start, 2026-10-31 10:00 PDT).

| | Base | Head | Change |
|---|--:|--:|--:|
| Laws, as the README's lead counts them | 1,016 | 1,488 | +472 |
| … about running code | 787 (77%) | 1,345 (90%) | +558 |
| … that run the node's code in a World | 10 | 68 | +58 |
| … not yet about running code | 219 | 75 | -144 |
| Proof steps (lemmas a law about running code uses; counted apart) | — | 63 |  |
| Negative controls (laws that prove a mutant breaks its law) | 20 | 33 | +13 |
| README promises proven over running code (✅) | 40 | 62 | +22 |
| README promises partly proven (🟡) | 31 | 32 | +1 |
| README promises wanted, not proven (⬜) | 14 | 13 | -1 |
| `theorem` declarations in .lean files | 2,399 | 4,619 | +2,220 |
| .lean files | 362 | 684 | +322 |
| Lines of Lean | 77,516 | 126,463 | +48,947 |

- **Promises that changed mark** (same title at the base and the head): ✅ → 🟡: "A removed member's node stops holding the community, and can rejoin only as a new device"; 🟡 → ✅: "A removal ends a live session's sync", "Peers cannot push ops in", "Judging cannot be hung", "Honest nodes agree", "Purge is safe", "Purge takes exactly what it must"; ⬜ → 🟡: "Everyone converges". 32 promises at the head have a title the base does not have (new or reworded).
- **Vacuity** at the base: no report (README.md has no "Vacuity check reports").
- **Vacuity** at the head: of 841 declarations the README links, 527 have a concrete input checked by Lean's kernel and 193 one checked by running the code; 31 are conditional on a named assumption; 90 are pending: `oneOpPerId_of`, `notice_local`, `caughtUp_local`, `exec_current`, `responder_opens_none`, `shipped_controls_apply`, `local_within`, `background_within`, `take_vacant`, `converge`, `offline`, `want_reaches`, `drain`, `want_to_op`, `op_hop`, `write_hop`, `step_waits`, `grows`, `deliver_wants`, `deliver_queues`, `deliver_takes`, `onSealed_wants`, `onSealed_queues`, `onSealed_takes`, `onSealed_waits`, `onTick_moves`, `serve_moves`, `onHold_wants`, `recv_asked`, `recv_owed`, `recv_appends`, `node_serve`, `request_again`, `shipped_late`, `bottoms_eq`, `rowAt_iff`, `notifies_iff`, `can_alert`, `once`, `step_quiet`, `target_opens`, `keepSync_keeps`, `keepSync_set`, `unmount_keeps_node`, `acts_shown`, `inv_pass`, `Costs.time`, `list_costs`, `model_fits`, `id_bind`, `run_bind`, `run_fresh`, `fair_loss_delivered`, `empty_log_agrees`, `nodup`, `nodup_full`, `sum_map_add`, `Costs.mono`, `costs_bind`, `costs_bindP`, `within_bind`, `within_bindP`, `cr_erase`, `within_at`, `eval_partition`, `lexCmp_append_zero`, `of_map`, `to_map`, `Reads.mono`, `leftOps_eq_some`, `leftOps_isSome`, `fill_index`, `source_iff`, `tile_phase`, `inserts_size`, `filter_idxOf_le`, `finite_eventually_held`, `keeps`, `retains`, `settled`, `budget_same_ops`, `dedup_nodup`, `ins_sorted`, `mem_inserts`, `Session.closed_terminal`, `same_inputs`, `Symbolic.good`, `eligible_spec`, `RetryOrder.filter_rank`, `SeekCost.seek`.
- **docs/CAUGHT.md** at the base: absent.
- **docs/CAUGHT.md** at the head: "Caught by a law": 4 (A user's own write could wait behind the reader's backlog (2026-11-01); Back to the switcher lost its backdrop (566e566, 2026-10-31); A replayed handshake retired a live session (found 2026-10-28; fix not on main); A crash kept a session's keys in the store for good (found 2026-10-31)). "Found otherwise, pinned by a law afterwards": 8, of which 3 say they are pinned by a test, not yet a law.
- **Lean toolchain** (lean-toolchain): base v4.34.0; head v4.35.0.
- **Build and judging files** at the base: no Makefile; no comparator.json; no LICENSE file.
- **Build and judging files** at the head: a Makefile with targets `help`, `install`, `run`, `online`, `demo`, `check`, `assets`, `verify`; comparator.json with 18 theorems, permitted axioms `propext`, `Quot.sound`, `Classical.choice`; a LICENSE file.
- **Commits** since the base: 710, of which 181 are merges. 6 were authored before the start (on 2026-10-28): `63f5317a`, `dbb0ff53`, `df760433`, `a0e735dd`, `d9c6eaaa`, `aa2fb401` (merged in `94e900da`).
- **Files changed** since the base: 1,281 (+135,629 lines, -24,881 lines).
<!-- hackathon:end -->

- A law is **about running code** when every definition its statement
  names runs from the app's `main` or the node's runner, or is proven
  equal to code that does.
- A law **in a World** runs the node's own code over a modelled network.
- `tests/wiring-models.txt` lists every law the check still counts as
  over a model; the wiring check fails on any other model law, and the
  list can only get shorter (theme 10). Some of the laws added since the
  base, in the fair-service and liveness work (theme 3), are stated over
  run harnesses such as `Execution`, and are on that list.
- A **negative control** is a law that proves a mutant of the code breaks
  a law. It shows that the law rejects bad code.
- A **README promise** is a row of the README's guarantee tables: ✅
  proven over running code, 🟡 partly proven, ⬜ wanted.
  `ci/proof-links.py` checks that a ✅ row cites a law about running code,
  and that a 🟡 row says what is missing.
- The numbers count main as it is. So they include the six commits that
  were written before the start (see "Work from before the start").

**Refresh before submission.** On a checkout of the submitted commit,
run `mise run hackathon:refresh` (`python3 ci/hackathon.py --refresh`).
It writes the block above from git, commits this file alone, and then
runs the script's self-test and `--check`. `python3 ci/hackathon.py
--head REV` prints the block for any commit REV, and `--write --head REV`
writes it here. `mise run hackathon:check` fails when anything but this
file has changed since the commit that the block names.

## What changed

1. **Vacuity audit: a concrete input for every linked law.** A law with
   hypotheses that can never hold together proves nothing. For each
   declaration that the README links, a check builds a concrete input that
   meets every hypothesis and applies the law to it. Lean's kernel checks
   most of these. The rest run the native code and check the result. Some
   stay conditional on a named assumption, such as Ed25519 unforgeability,
   which a finite check cannot prove. The audit started at
   [`74dea236`][74dea236]. By [`b8387523`][b8387523], each of the 511
   declarations linked then had an entry: a witness, a conditional check
   that names its open assumption, or a counterexample. It found two
   premises that the native crypto did not meet (theme 2). See
   [tests/vacuity/](../tests/vacuity), [ci/vacuity.py](../ci/vacuity.py)
   and the README's "Vacuity check reports". `mise run test:vacuity` runs
   in the gate. The block above gives the coverage at the head and names
   the laws still pending.

2. **Crypto contracts that the code meets, and sized keys.** The audit
   showed that `Seal.Good` and Noise's `Suite.Good` were false of the
   native crypto. For example, a key of the wrong size sealed to empty
   bytes ([`5c1d4036`][5c1d4036]). So the laws that assumed them could not
   apply to the running code. The contracts now cover only the sizes that
   the crates support ([`0b59f14c`][0b59f14c], [`e48edb27`][e48edb27]).
   Native seal errors now reach the caller ([`208d4199`][208d4199]), and
   the AEAD bounds respect the cipher's counter limit
   ([`cd4d7c84`][cd4d7c84]). Then keys and nonces became sized types
   (`Bytes 32`, `Bytes 24`), so no law needs a size premise
   ([`67cfc08a`][67cfc08a], merged in [`e770ab94`][e770ab94]). What the
   proofs trust about the crypto crates is one file of named premises,
   never axioms: [engine/core/Trust.lean](../engine/core/Trust.lean).
   [tests/vacuity/CryptoTrust.lean](../tests/vacuity/CryptoTrust.lean)
   checks that the native crates meet each premise and that a broken model
   does not. The same pattern now covers SQLite
   ([engine/core/StoreTrust.lean](../engine/core/StoreTrust.lean),
   [`728c5cb0`][728c5cb0]), and the wiring check fails on an `@[extern]`
   without a stated contract ([`755254b2`][755254b2]).

3. **Fair service, with local work first.** The node's loop now serves
   local writes, network events and ticks fairly ([`1b334291`][1b334291]),
   and gives local work priority with a bounded share for sync
   ([`d90dc7c5`][d90dc7c5], [`00baa2c5`][00baa2c5],
   [`60de8ab6`][60de8ab6]). The laws say that three of every four polls
   prefer local writes (`Priority.local_share`). A waiting local write is
   chosen within 2 polls per place in its queue, and a network event
   within 4 per place, even while local writes keep coming
   (`Priority.write_within`, `Priority.event_within`). The write bound
   still holds with per-peer fairness for inbound frames
   (`Prioritized.write_within`). The laws are in
   [engine/wire/PriorityLaws.lean](../engine/wire/PriorityLaws.lean) and
   [engine/wire/IngressPriorityLaws.lean](../engine/wire/IngressPriorityLaws.lean).
   For a join, a successful run of the node's own code, with the real
   connection hooks and native crypto, continues with an infinite fair run
   (`successful_fair_extension`, `Execution.fairRun_fair`, World laws;
   [`a785a9ee`][a785a9ee], [`5aadd831`][5aadd831]). `mise run
   test:fairness` runs the real encrypted runner over TCP, with negative
   controls. **Limits:** some laws here are still stated over run
   harnesses (see `tests/wiring-models.txt`). Not proven yet: convergence for every fair run of the app, and bounds
   from a commit to the screen. See
   [docs/EXECUTION-PROGRESS.md](EXECUTION-PROGRESS.md) and
   [docs/BOOTSTRAP-LIVENESS.md](BOOTSTRAP-LIVENESS.md).

4. **Forensics fixes: laws restated over the code that runs.** An audit of
   main at [`0958e672`][0958e672] looked for premises that the running
   code cannot meet, and for laws weaker than their README rows. The fixes
   ([`3dd5a416`][3dd5a416], [`316ded1c`][316ded1c], merged in
   [`b4d103a9`][b4d103a9]):
   - `Unforgeable` covered every signature that could exist. So it could
     hold only if every message counted as signed, and the laws that used
     it said nothing about who signed. It now covers the signatures in the
     store (`unscoped_signs_all` is the old form's negative control).
   - The attachment laws assumed no second preimage of SHA-256, which is
     false. They now assume no collision among the hashes at hand
     (`Merkle.NoCollision`), and a test decides that on real SHA-256.
   - The desktop layout laws are now about `zoomLayout` at every density,
     which the driver paints, not about `layout` at one density.
   - `mutual_removal` now derives both removals from signed ops instead of
     assuming them, weak vacuity witnesses got real conclusions, and
     unused premises went.
   - The bootstrap model went, with its laws: nothing that runs imported
     it ([`147a0d2e`][147a0d2e]; [docs/NET.md](NET.md)).

5. **Removal reaches every live session, and ended sessions leave no
   keys.** In every entry point of the node, each connection step reads
   its rooms afresh (`entry_fresh`, [`6628b514`][6628b514]). Each frame
   sealed for a removed member's session carries, of that community, only
   sync messages and the removal with the ops it requires, and then the
   session closes (`removal_reaches_session`, [`5970dab1`][5970dab1]). The
   README row "A removal ends a live session's sync" was 🟡 at the base and
   is ✅ now. It became ✅ when the purge bridge, written before the start,
   was merged: then these laws counted as about running code (see "Work
   from before the start"). The row "No packet goes to a removed member
   but the notice of its removal" stays 🟡: the bare handshake replies are
   proven per step only. One promise went from ✅ to 🟡: "A removed member's
   node stops holding the community". A removed user's invitations and
   approvals stay valid, so it can admit a new device of its own, and the
   README now says so ([`4e23e2f6`][4e23e2f6]).

   A retiring session now reads to the peer's end, so the removed peer
   gets its notice ([`8a8a0191`][8a8a0191]). Every ended session's keys
   are purged, also after a crash (`close_forgets`, `purge_forgets`,
   `forget_stays`, `retired_complete`; [`50176d41`][50176d41]). A law
   found the crash case: see [docs/CAUGHT.md](CAUGHT.md). The row "A
   closed session's keys cannot be recovered" stays 🟡: it assumes that a
   deleted row leaves no bytes on disk, and it does not cover a phone
   backup. Saving a checkpoint now deletes the older ones, which held
   invite seeds and drafts ([`50176d41`][50176d41]). On SQLite, a purge
   runs as the model's purge, under SQLite's stated contract
   (`purge_as_model`, [`f5312c9a`][f5312c9a]). The test that deleted rows
   leave no bytes on disk (`mise run test:engine`) is older than the base.

6. **The glyph memo is proven.** At the base, the glyph cache was an
   `unsafe` seam behind `implemented_by`, and its equality with the raster
   was tested, not proven. Now each font source keeps a lazy table of
   thunks, and `@[csimp]` `bitmap_eq_fast` proves that what the compiler
   runs equals rastering the glyph, with no `unsafe` and no
   `implemented_by` (`Table.get_eq`; `shifted_not_exact` is its negative
   control). See
   [engine/renderer/Ttf/Memo.lean](../engine/renderer/Ttf/Memo.lean) and
   [docs/NOTO.md](NOTO.md) ([`2e428a96`][2e428a96],
   [`33c0ffe3`][33c0ffe3], [`5a8dcbaf`][5a8dcbaf]). **Limit:** the old
   cache had a 4 MiB bound. The memo keeps each glyph until the app
   rebuilds its fonts (on suspend and on a density change), so a memory
   bound is "not yet" in the README.

7. **UI work on iOS, Android and desktop.**
   - iOS: UIKit owns conversation scrolling and deceleration
     ([`841954f1`][841954f1]), a fling keeps its speed
     ([`8fe0bff2`][8fe0bff2]), and press timing uses UIKit's clock, tested
     with real short touches ([`c59090b2`][c59090b2]).
   - Android: the activity and keyboard survive recreation
     ([`1bb5a53f`][1bb5a53f]), editor actions go through admission
     ([`8bd282c7`][8bd282c7]), and a retired owner cancels its own photo
     request ([`2ee6e4a3`][2ee6e4a3]).
   - Desktop: `leanquiet://` invite links reach the Linux and macOS apps
     ([`92e6ee1e`][92e6ee1e]), the scrollbar is placed by message rank,
     with laws ([`519dd957`][519dd957]), and a new native Windows shell
     runs the same Lean app ([`00dfdfb0`][00dfdfb0];
     [platforms/windows](../platforms/windows/README.md)).
   - Shared screens: the phones' community switcher and the Get started
     screen follow Quiet's design ([`566e5664`][566e5664],
     [`4c5dd94d`][4c5dd94d]). The law "Back goes back" caught a bug in the
     switcher change ([`e62ab114`][e62ab114];
     [docs/CAUGHT.md](CAUGHT.md)).

8. **Lean 4.35, Comparator and `make`.** The block above reads these
   from the commit it names: the Lean toolchain (`lean-toolchain`), the
   Makefile's targets (the rules ask for `make install && make run`),
   `comparator.json` (the headline laws that Comparator checks, and the
   axioms it permits), and the LICENSE file. Where the block says "no
   Makefile" or "no comparator.json", that part is not in the commit.
   The headline laws and how to check them are in `docs/HEADLINE.md`
   when `comparator.json` is there.

9. **README claims made exact, and SQLite's part written down.** The
   README's headline claims were checked against the wiring check and
   corrected where they said more or less than the laws prove. A new
   section, "What the proofs assume of SQLite", lists what the proofs
   take of the database and how each part is met, and the store now
   commits with `synchronous=FULL`, so a committed turn survives power
   loss. A test and a negative control check that setting.

10. **Laws over models, ratcheted down.** `tests/wiring-models.txt` lists
    the laws the wiring check still counts as over a model. The check
    fails on any law over a model that is not on the list, and the list
    can only get shorter. Many model laws were restated over the running
    code or deleted, and lemmas that a law about running code uses are
    counted apart as "proof steps". The block above has the counts at the
    submitted commit.

**Also on main.** The op tree: each op type is a folder with its
validator, and [ci/layout.py](../ci/layout.py) checks the layout
([`930b39f3`][930b39f3], [`04322c45`][04322c45], [`db9eaf6f`][db9eaf6f]).
An n-node World: convergence over any network of nodes, given a delivery
bound per edge; the World count above includes it ([`6410107b`][6410107b],
[`8c8375b1`][8c8375b1]). One approval admits a member; invitation
thresholds are gone ([`4e23e2f6`][4e23e2f6]). A fast gate before every
push to main, and landing through `ci/land.sh` ([`5a49489d`][5a49489d],
[`a105a8ce`][a105a8ce]). Invite links through a join page, and Linux and
macOS release scripts ([`0cdc5982`][0cdc5982], [`fb66dee0`][fb66dee0];
[docs/RELEASE.md](RELEASE.md)).

## Work from before the start

- Six commits on main were authored on 2026-10-28, before the start: the
  purge bridge (branch `fd/purge-bridge`). It proves that the running
  purge is the model's purge (`run_purge`). It was merged during the
  hackathon, in [`94e900da`][94e900da], and that merge needed new work to
  build on the new main (its message says what). The block above lists the
  six commits.
- The bridge made more laws count as about running code. On its branch, it
  moved 23 laws ([`a0e735dd`][a0e735dd]). At the merge, six README
  promises went from 🟡 to ✅: "A removal ends a live session's sync",
  "Peers cannot push ops in", "Judging cannot be hung", "Honest nodes
  agree", "Purge is safe" and "Purge takes exactly what it must". The
  block above lists these with the other changes of mark. The numbers
  count main as it is, so they include this work.
- One entry in "Caught by a law" in [docs/CAUGHT.md](CAUGHT.md), the
  replayed handshake, was found on 2026-10-28. Its fix is not on main.
- Everything at the base: see "What existed at the base".

## In progress

Nothing in this section is in the submitted commit. Each item names its
branch.

- `vibecheck/mac`: `make install && make run` on macOS.


## Changed after the submission

The submitted version is the tag `vibecheck-submission`. After it, one
wire break fixed two audit findings, as the user decided. Wraps are
signed, and a community has one content key: its root names the key's
id, and every admission carries it. A removal records the approval chain
heads it saw, and trust counts only approvals inside every removal's cut
(the causal cut). Four headline statements in
[tests/comparator/Challenge.lean](../tests/comparator/Challenge.lean)
changed with it:
- `no_impersonation`: the admission it names has the key id field
  (existential, so no weaker).
- `admission_needs_approval`: it names the richer approval fact
  (`g : Approve.Fact`), equivalent to the old form.
- `removal_authorized`: the removal takes its cut (implicit); the
  conclusion is the same.
- `connect_iff`: the stricter trust rule, `Trusted ∧ Live` instead of
  `Admitted ∧ Live`. Trusted implies admitted
  ([`Trusted.admitted`](../app/community/Proofs.lean#L1557)), so acceptance says more;
  the converse is narrower on purpose: an admission approved outside a
  removal's cut no longer lets a node in.

`deviceCut_removal`, a headline law added after the submission, names
the admission with its key id too.

[89914bea]: https://github.com/holmesworcester/lean-quiet/commit/89914bea346ddf93d9a065a2e8bef0c79ed47797
[5825ebc3]: https://github.com/holmesworcester/lean-quiet/commit/5825ebc37eb1fdd38c7d00408d91da3148fa2749
[74dea236]: https://github.com/holmesworcester/lean-quiet/commit/74dea2361edfe17ea860812302b6617f271e6fd5
[b8387523]: https://github.com/holmesworcester/lean-quiet/commit/b83875239ee0574e43acdb09b2be40b888c26394
[5c1d4036]: https://github.com/holmesworcester/lean-quiet/commit/5c1d40361e707a8006442bf939ccef7572fc0c66
[0b59f14c]: https://github.com/holmesworcester/lean-quiet/commit/0b59f14c765ce14269ca7042d36b3c46a79ea1a0
[e48edb27]: https://github.com/holmesworcester/lean-quiet/commit/e48edb27f9057ac3cb6df3dc87e220ce430651ed
[208d4199]: https://github.com/holmesworcester/lean-quiet/commit/208d4199f7b3ddce8d9bd40235901b73361a7578
[cd4d7c84]: https://github.com/holmesworcester/lean-quiet/commit/cd4d7c84e15ec89dc2f42e54072b4a4f7b7d96a8
[67cfc08a]: https://github.com/holmesworcester/lean-quiet/commit/67cfc08ab3e1590a3fe3753d644639159479e17d
[e770ab94]: https://github.com/holmesworcester/lean-quiet/commit/e770ab94f6ca7eb973097e699787f87bb9127347
[728c5cb0]: https://github.com/holmesworcester/lean-quiet/commit/728c5cb04986a3d44d258b3275e6c2c15e90339f
[755254b2]: https://github.com/holmesworcester/lean-quiet/commit/755254b28c2be2849457432b90158ea3c1048713
[1b334291]: https://github.com/holmesworcester/lean-quiet/commit/1b3342917a3d2ea8e7aa4111382623f2fd11231d
[d90dc7c5]: https://github.com/holmesworcester/lean-quiet/commit/d90dc7c51e0972acd76500ef02d8daabfa62ed71
[00baa2c5]: https://github.com/holmesworcester/lean-quiet/commit/00baa2c5c2c12c08ca7c962337e95be89cef8b6b
[60de8ab6]: https://github.com/holmesworcester/lean-quiet/commit/60de8ab6ea6b43f00a08d9291962b9fe3f2b2756
[a785a9ee]: https://github.com/holmesworcester/lean-quiet/commit/a785a9eed18654aa7dc4d113f81e8afbae6fcbd1
[5aadd831]: https://github.com/holmesworcester/lean-quiet/commit/5aadd831411c0b6a2236dffd64ef88c0f72303bc
[0958e672]: https://github.com/holmesworcester/lean-quiet/commit/0958e672c56cf55cc06b9fbd593bad0ec8e8db61
[3dd5a416]: https://github.com/holmesworcester/lean-quiet/commit/3dd5a4165622d54889ac65258599deb55ff28fce
[316ded1c]: https://github.com/holmesworcester/lean-quiet/commit/316ded1c9142abeb56cab64151fc0e896f51231e
[b4d103a9]: https://github.com/holmesworcester/lean-quiet/commit/b4d103a9f9a342d3f2d4f5b0fca89f1722b5b2af
[147a0d2e]: https://github.com/holmesworcester/lean-quiet/commit/147a0d2edcd0202b25e2b450fb7428769de91ba0
[6628b514]: https://github.com/holmesworcester/lean-quiet/commit/6628b51453aae0d301765e0f69fe33cc0bca9115
[5970dab1]: https://github.com/holmesworcester/lean-quiet/commit/5970dab1db6d3991b2ea0fa54a3fd34587636f84
[4e23e2f6]: https://github.com/holmesworcester/lean-quiet/commit/4e23e2f664689f65a9b5c44c0803753845523f2d
[8a8a0191]: https://github.com/holmesworcester/lean-quiet/commit/8a8a01912c16ac2660a50b72a21e147d5e2add6f
[50176d41]: https://github.com/holmesworcester/lean-quiet/commit/50176d41e05869009aa6bac6f6a2dde21f2e8bf5
[f5312c9a]: https://github.com/holmesworcester/lean-quiet/commit/f5312c9a47bdb0b4b91ba74a54d643e6f904b09e
[2e428a96]: https://github.com/holmesworcester/lean-quiet/commit/2e428a96374a56f928dde66d028f7ad2b2688f5e
[33c0ffe3]: https://github.com/holmesworcester/lean-quiet/commit/33c0ffe3e5eb947b942c2fb362fe30e91f48a752
[5a8dcbaf]: https://github.com/holmesworcester/lean-quiet/commit/5a8dcbafe7b7839e5aee748bf0fea9bb156a6146
[841954f1]: https://github.com/holmesworcester/lean-quiet/commit/841954f1839df1747d58a6ece49af9f0c1514900
[8fe0bff2]: https://github.com/holmesworcester/lean-quiet/commit/8fe0bff2e468ac8db493df886c4f55c70a19bcf5
[c59090b2]: https://github.com/holmesworcester/lean-quiet/commit/c59090b255f5e41ed6056a9ce632dfd22d55845c
[1bb5a53f]: https://github.com/holmesworcester/lean-quiet/commit/1bb5a53f9f1c0c3dc6f3a38b2de9c6e7f8309454
[8bd282c7]: https://github.com/holmesworcester/lean-quiet/commit/8bd282c7beb064e43260522b83ff897a752083e3
[2ee6e4a3]: https://github.com/holmesworcester/lean-quiet/commit/2ee6e4a38b132830c02c3fefa774a89e04019907
[92e6ee1e]: https://github.com/holmesworcester/lean-quiet/commit/92e6ee1e408c2028f977c08df1a2449111ce15a6
[519dd957]: https://github.com/holmesworcester/lean-quiet/commit/519dd9578cbd0b42c30e4b0ab1f744b5e03e23f5
[00dfdfb0]: https://github.com/holmesworcester/lean-quiet/commit/00dfdfb04cc19db3f3c4595ee08832492467b312
[566e5664]: https://github.com/holmesworcester/lean-quiet/commit/566e56647ac37f165fb26e11024c5a39f2176621
[4c5dd94d]: https://github.com/holmesworcester/lean-quiet/commit/4c5dd94d0692f9f4197bac3264771058a328d920
[e62ab114]: https://github.com/holmesworcester/lean-quiet/commit/e62ab114d564234f923b604a76bb67696f4eec9a
[930b39f3]: https://github.com/holmesworcester/lean-quiet/commit/930b39f35b729c5da31f70788ae801424a88a7d9
[04322c45]: https://github.com/holmesworcester/lean-quiet/commit/04322c45467731480d6ba5faadc0a8939e3c5ef6
[db9eaf6f]: https://github.com/holmesworcester/lean-quiet/commit/db9eaf6fe4f2ca4c0f462d0b824de0d806f674dc
[6410107b]: https://github.com/holmesworcester/lean-quiet/commit/6410107b217621928fddac82d4a649f108fa6875
[8c8375b1]: https://github.com/holmesworcester/lean-quiet/commit/8c8375b1413bf652eceffbf3ba754892182a7d12
[5a49489d]: https://github.com/holmesworcester/lean-quiet/commit/5a49489d0f400f810d79bddd75ce2129c603515c
[a105a8ce]: https://github.com/holmesworcester/lean-quiet/commit/a105a8ce78eaa5a16dc8e81f1264a5422b80050e
[0cdc5982]: https://github.com/holmesworcester/lean-quiet/commit/0cdc5982b518d0202cf90a38277e9fb53f534f05
[fb66dee0]: https://github.com/holmesworcester/lean-quiet/commit/fb66dee0c5139cbbee8b1344a3e8b023e21b8d1b
[94e900da]: https://github.com/holmesworcester/lean-quiet/commit/94e900da68dae84aecbd155f4bae49f1e32527a2
[a0e735dd]: https://github.com/holmesworcester/lean-quiet/commit/a0e735dd03e9d9709c244e59ec4477c95ca9f375
[5c1da634]: https://github.com/holmesworcester/lean-quiet/commit/5c1da634dc5298c80d30673a99d0e4a2f8093e69
