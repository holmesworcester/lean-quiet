# The proof tree

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

How the laws compose: each law opens to the laws its proof uses. The headlines are the laws the [README](../README.md#what-is-proven)'s guarantee rows cite, each a tree in the file of its table group. A law is drawn whole once, and links there (↪) elsewhere; *n below* counts the distinct laws a law builds on.

✅ wired: about running code (1345) · 🌐 world: the node's code in a World (68) · 🪜 step: a step of a wired law (61) · 📐 model: over a model (71) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2127)

## Scoreboard

Composing the proofs into one tree lowers the roots and isolated laws, and raises the share the headlines build on.

| | |
|---|---|
| Laws | 3705 |
| Edges (a proof uses a law) | 9839 |
| Roots (no law uses them) | 1100 (29.7%) |
| Isolated (roots that use no law) | 528 (14.3%) |
| Deepest chain | 23 |
| Median chain | 1 |
| Headlines (laws the README's guarantee rows cite) | 632 |
| Laws the headlines build on, or are | 2475 (66.8%) |

## Headlines

| Group | Headlines | Laws drawn there |
|---|---|---|
| [Security proofs › Identity and membership](proof-tree/security-proofs-identity-and-membership.md) | 24 | 61 |
| [Security proofs › Confidentiality](proof-tree/security-proofs-confidentiality.md) | 60 | 228 |
| [Security proofs › Connections](proof-tree/security-proofs-connections.md) | 60 | 243 |
| [Security proofs › Hostile input](proof-tree/security-proofs-hostile-input.md) | 66 | 173 |
| [Quality proofs › The engine](proof-tree/quality-proofs-the-engine.md) | 65 | 200 |
| [Quality proofs › Sync](proof-tree/quality-proofs-sync.md) | 150 | 447 |
| [Quality proofs › The screen](proof-tree/quality-proofs-the-screen.md) | 208 | 385 |
| [Quality proofs › Codes, pictures and discovery](proof-tree/quality-proofs-codes-pictures-and-discovery.md) | 13 | 30 |
| [Also cited](proof-tree/also-cited.md) | 92 | 122 |

## Uncited roots

Laws no law uses and the README does not cite: 699, 421 of them isolated (they use no law either). Each is a claim of its own or a dead end; composing them into the headlines' trees, or deleting them, shrinks this list.

| Folder | Laws | Uncited roots | Isolated |
|---|---|---|---|
| app | 361 | 68 | 39 |
| app/community | 241 | 46 | 12 |
| app/community/caughtUp | 3 | 3 | 1 |
| app/community/channel/message | 28 | 12 | 9 |
| app/community/channel/message/attachment | 61 | 29 | 16 |
| app/community/channel/message/attachment/chunk | 10 | 5 | 1 |
| app/community/channel/message/draft | 28 | 6 | 3 |
| app/community/channel/message/reaction | 15 | 4 | 2 |
| app/community/channel/message/receipt | 14 | 7 | 5 |
| app/community/device/endpoint | 8 | 3 | 1 |
| app/community/device/secret | 6 | 5 | 2 |
| app/community/key | 4 | 4 | 2 |
| app/community/key/wrap | 10 | 8 | 6 |
| app/community/member/admin | 7 | 3 | 1 |
| app/community/member/invite | 45 | 4 | 0 |
| app/community/member/invite/request | 8 | 3 | 1 |
| app/community/member/invite/request/approve | 8 | 3 | 1 |
| app/community/member/invite/request/approve/admit | 2 | 1 | 1 |
| app/community/member/join/accept | 4 | 3 | 1 |
| app/community/member/join/joining | 4 | 3 | 1 |
| app/community/member/join/joining/abandon | 5 | 4 | 3 |
| app/community/member/remove | 12 | 3 | 1 |
| app/community/name | 5 | 3 | 1 |
| app/community/notice | 8 | 4 | 2 |
| app/community/profile | 11 | 5 | 3 |
| app/connection | 64 | 5 | 3 |
| app/connection/connection | 5 | 3 | 1 |
| app/connection/eph | 3 | 3 | 1 |
| app/connection/established | 5 | 4 | 3 |
| app/connection/given | 3 | 3 | 1 |
| app/connection/opened | 6 | 4 | 3 |
| app/connection/recv | 3 | 3 | 1 |
| app/connection/request | 4 | 4 | 2 |
| app/connection/send | 4 | 3 | 1 |
| app/nav | 11 | 2 | 2 |
| app/settings/appearance | 14 | 3 | 2 |
| engine/core | 742 | 113 | 78 |
| engine/renderer | 401 | 132 | 89 |
| engine/renderer/Ttf | 16 | 7 | 6 |
| engine/renderer/qr | 58 | 5 | 4 |
| engine/sync | 586 | 58 | 25 |
| engine/wire | 529 | 86 | 72 |
| engine/wire/mdns | 43 | 5 | 4 |
| engine/world | 272 | 17 | 8 |

<details><summary><b>app</b> · 68</summary><ul>
<li>✅ <a href="../app/Screen.lean#L3817">App.composer_no_selection</a> · isolated</li>
<li>✅ <a href="../app/Screen.lean#L3812">App.composer_pending_feedback</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1535">App.screenChanged_insets</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1529">App.screenChanged_size</a> · isolated</li>
<li>✅ <a href="../app/Screen.lean#L1924">Appearance.selected_check</a> · isolated</li>
<li>✅ <a href="../app/Screen.lean#L1582">ClumpList.cells_bounded</a> · isolated</li>
<li>✅ <a href="../app/Screen.lean#L1588">ClumpList.extent_cells</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L2496">Connection.Execution.GoesM.getStatus'</a> · 3 below</li>
<li>▫️ <a href="../app/Proofs.lean#L3212">Connection.Execution.HistoryM.getOp'</a> · 2 below</li>
<li>▫️ <a href="../app/Proofs.lean#L3214">Connection.Execution.HistoryM.getStatus'</a> · 2 below</li>
<li>📐 <a href="../app/Proofs.lean#L3167">Connection.Execution.HistoryStep.catalog_read</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L3175">Connection.Execution.HistoryStep.ceiling_mono</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L2174">Connection.Execution.M.pure_apply</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L3439">Connection.Execution.Run.history</a> · 230 below</li>
<li>📐 <a href="../app/Proofs.lean#L2823">Connection.Execution.Run.shared_retained</a> · 152 below</li>
<li>📐 <a href="../app/Proofs.lean#L3427">Connection.Execution.empty_trace_history</a> · 233 below</li>
<li>▫️ <a href="../app/Proofs.lean#L2190">Connection.Execution.lawful</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L2740">Connection.Execution.production_step_reachable</a> · 142 below</li>
<li>📐 <a href="../app/Proofs.lean#L2734">Connection.Execution.production_step_retains</a> · 150 below</li>
<li>📐 <a href="../app/Proofs.lean#L2747">Connection.Execution.production_step_settled</a> · 174 below</li>
<li>📐 <a href="../app/Proofs.lean#L3129">Connection.Execution.production_write_receives</a> · 164 below</li>
<li>▫️ <a href="../app/Proofs.lean#L2195">Connection.Execution.reads_meta</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L2200">Connection.Execution.save_meta</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L2263">Connection.Progress.Exchange.answer_constructed</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L2301">Connection.Progress.Exchange.initiator_accepts</a> · 29 below</li>
<li>✅ <a href="../app/Proofs.lean#L2283">Connection.Progress.Exchange.opened_accepts</a> · 29 below</li>
<li>✅ <a href="../app/Proofs.lean#L2277">Connection.Progress.Exchange.reply_accepts</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L2270">Connection.Progress.Exchange.request_accepts</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L2259">Connection.Progress.Exchange.request_constructed</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L2291">Connection.Progress.Exchange.responder_accepts</a> · 29 below</li>
<li>✅ <a href="../app/Proofs.lean#L2380">Connection.Progress.answer_ready</a> · 40 below</li>
<li>✅ <a href="../app/Proofs.lean#L2315">Connection.Progress.honest_exchange</a> · 38 below</li>
<li>✅ <a href="../app/Proofs.lean#L2364">Connection.Progress.react_contains_answer</a> · 47 below</li>
<li>📐 <a href="../app/Proofs.lean#L2439">Connection.ProgressTape.answer_ready</a> · 37 below</li>
<li>📐 <a href="../app/Proofs.lean#L2429">Connection.ProgressTape.run_arrivedFrom</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L2414">Connection.ProgressTape.run_bind</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L2417">Connection.ProgressTape.run_count</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L2433">Connection.ProgressTape.run_fresh</a> · isolated</li>
<li>📐 <a href="../app/Proofs.lean#L2420">Connection.ProgressTape.run_get</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1069">Connection.reconnect_dials_each</a> · 37 below</li>
<li>✅ <a href="../app/Proofs.lean#L1050">Connection.rejoin_dials_each</a> · 37 below</li>
<li>▫️ <a href="../app/Proofs.lean#L778">Connection.resendConns_send</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L3822">Connection.retired_open</a> · 6 below</li>
<li>✅ <a href="../app/Proofs.lean#L3539">Connection.secret_unfiled</a> · isolated</li>
<li>🧪 <a href="../app/Proofs.lean#L3846">Connection.shipped_retired_misses</a> · 4 below</li>
<li>✅ <a href="../app/Commands.lean#L619">Data.overlay_total</a> · isolated</li>
<li>✅ <a href="../app/Screen.lean#L279">Lifecycle.follow_away</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1359">NavLaws.draft_open</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1371">NavLaws.inv_back</a> · 1 below</li>
<li>✅ <a href="../app/Proofs.lean#L1374">NavLaws.inv_switch</a> · 2 below</li>
<li>🧪 <a href="../app/Proofs.lean#L1420">NavLaws.shipped_back_open_fails</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L4118">Pages.getStarted_taps</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L4124">Pages.startTaps_rows</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L4075">Pages.start_centred</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L4083">Pages.start_column_inside</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L4065">Pages.start_phone</a> · isolated</li>
<li>▫️ <a href="../app/Proofs.lean#L4105">Pages.start_rows_apart</a> · 2 below</li>
<li>▫️ <a href="../app/Proofs.lean#L4090">Pages.start_rows_in_card</a> · 3 below</li>
<li>✅ <a href="../app/Family.lean#L54">Quiet.node_settings</a> · 2 below</li>
<li>✅ <a href="../app/Proofs.lean#L1503">RemovedLaws.forget_clears</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1493">RemovedLaws.landing_listed</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1457">RemovedLaws.listed_iff</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1483">RemovedLaws.not_replayed</a> · 1 below</li>
<li>✅ <a href="../app/Proofs.lean#L1465">RemovedLaws.told_once</a> · 1 below</li>
<li>✅ <a href="../app/Proofs.lean#L1559">ThemeLaws.cleared</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1573">ThemeLaws.content</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1568">ThemeLaws.palette</a> · isolated</li>
<li>✅ <a href="../app/Proofs.lean#L1586">ThemeLaws.text</a> · 5 below</li>
</ul></details>

<details><summary><b>app/community</b> · 46</summary><ul>
<li>▫️ <a href="../app/community/Family.lean#L1315">Community.All2.comp</a> · isolated</li>
<li>▫️ <a href="../app/community/Family.lean#L885">Community.Fact.decFrom_of</a> · 3 below</li>
<li>▫️ <a href="../app/community/Family.lean#L876">Community.Fact.dec_of</a> · isolated</li>
<li>▫️ <a href="../app/community/Op.lean#L222">Community.Root.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/Op.lean#L238">Community.Root.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/Op.lean#L246">Community.Root.all_args</a> · isolated</li>
<li>▫️ <a href="../app/community/Op.lean#L243">Community.Root.byDevice_args</a> · isolated</li>
<li>▫️ <a href="../app/community/Op.lean#L253">Community.Root.byKey_args</a> · isolated</li>
<li>▫️ <a href="../app/community/Op.lean#L249">Community.Root.byUser_args</a> · isolated</li>
<li>▫️ <a href="../app/community/Proofs.lean#L1921">Community.always_bindM</a> · 1 below</li>
<li>▫️ <a href="../app/community/Proofs.lean#L1918">Community.always_list</a> · isolated</li>
<li>✅ <a href="../app/community/Proofs.lean#L1780">Community.anchor_read</a> · 82 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L2013">Community.approveReq_authored</a> · 2 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1335">Community.approveReq_ops</a> · 1 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1755">Community.count_partition</a> · 13 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1941">Community.found_authored</a> · 3 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1994">Community.introduce_authored</a> · 2 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1958">Community.inviteTo_authored</a> · 2 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1971">Community.join_authored</a> · 4 below</li>
<li>▫️ <a href="../app/community/Proofs.lean#L1888">Community.mkOp_reqs</a> · isolated</li>
<li>✅ <a href="../app/community/Commands.lean#L430">Community.named_signs</a> · 1 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L2027">Community.react_reqs_le</a> · isolated</li>
<li>▫️ <a href="../app/community/Proofs.lean#L1526">Community.readable_listed</a> · 83 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L1043">Community.removals_at</a> · 63 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L2004">Community.removeMember_authored</a> · 2 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L2046">Community.send_authored</a> · 47 below</li>
<li>🧪 <a href="../app/community/Proofs.lean#L1414">Community.shipped_introduce_unnamed</a> · isolated</li>
<li>▫️ <a href="../app/community/Family.lean#L1008">Community.signedBy_ofApprove</a> · 24 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1006">Community.signedBy_ofAttach</a> · 31 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1002">Community.signedBy_ofGrant</a> · 24 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1000">Community.signedBy_ofInvite</a> · 26 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1009">Community.signedBy_ofName</a> · 31 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1010">Community.signedBy_ofNotice</a> · 31 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1004">Community.signedBy_ofPost</a> · 31 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1005">Community.signedBy_ofProfile</a> · 31 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1007">Community.signedBy_ofReact</a> · 31 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1003">Community.signedBy_ofRemove</a> · 24 below</li>
<li>▫️ <a href="../app/community/Family.lean#L1001">Community.signedBy_ofRequest</a> · 24 below</li>
<li>▫️ <a href="../app/community/Family.lean#L999">Community.signedBy_ofRoot</a> · 24 below</li>
<li>✅ <a href="../app/community/Proofs.lean#L634">Community.signed_eq</a> · isolated</li>
<li>✅ <a href="../app/community/Proofs.lean#L2021">Community.stopWaiting_authored</a> · isolated</li>
<li>🧪 <a href="../app/community/Proofs.lean#L1437">Community.wrapAll_over</a> · 2 below</li>
<li>✅ <a href="../app/community/Screen.lean#L363">Kinds.Accepted.read_known</a> · 1 below</li>
<li>✅ <a href="../app/community/Screen.lean#L484">PeopleLaws.presentCount_complete</a> · 3 below</li>
<li>✅ <a href="../app/community/Screen.lean#L462">PeopleLaws.presentW_prefix</a> · 7 below</li>
<li>🧪 <a href="../app/community/Screen.lean#L590">PeopleLaws.shipped_removed_without_removal</a> · 1 below</li>
</ul></details>

<details><summary><b>app/community/caughtUp</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/caughtUp/Op.lean#L24">Community.CaughtUp.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/caughtUp/Op.lean#L37">Community.CaughtUp.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/caughtUp/Op.lean#L44">Community.CaughtUp.byCommunity_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/channel/message</b> · 12</summary><ul>
<li>✅ <a href="../app/community/channel/message/Proofs.lean#L254">Community.Clump.backwards</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/Proofs.lean#L251">Community.Clump.expired</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/Proofs.lean#L248">Community.Clump.within_iff</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L31">Community.Post.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L82">Community.Post.Fact.enc_tag</a> · 36 below</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L92">Community.Post.all_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L94">Community.Post.byAuthor_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L99">Community.Post.byKey_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L105">Community.Post.childrenByKey_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/Op.lean#L102">Community.Post.rootsByKey_args</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/Proofs.lean#L93">Community.child_has_root</a> · 46 below</li>
<li>▫️ <a href="../app/community/channel/message/View.lean#L22">ViewLaws.id_bind</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/channel/message/attachment</b> · 29</summary><ul>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L370">ArrivalLaws.arrival_counts</a> · 11 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L269">ArrivalLaws.arrival_none</a> · 1 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L272">ArrivalLaws.arrival_some</a> · 3 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/Screen.lean#L52">ArrivalLaws.file_whole</a> · 113 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L228">ArrivalLaws.layout_inside</a> · 3 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L200">ArrivalLaws.layout_percent_lt</a> · 4 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L284">ArrivalLaws.layout_progress</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L51">ArrivalLaws.percent_eq</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L278">ArrivalLaws.picBox_progress</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/Screen.lean#L68">ArrivalLaws.pic_complete_iff_held</a> · 115 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L239">ArrivalLaws.ring_inside</a> · 2 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L301">ArrivalLaws.shown_pre</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/View.lean#L250">ArrivalLaws.words_inside</a> · 1 below</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Op.lean#L36">Community.Attach.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Op.lean#L56">Community.Attach.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Op.lean#L61">Community.Attach.byMessage_args</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/Proofs.lean#L34">Community.chunk_hangs_off</a> · 48 below</li>
<li>🧪 <a href="../app/community/channel/message/attachment/Screen.lean#L439">Pics.imageV_over_budget</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L388">Pics.run_bind</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L406">Pics.run_chunks</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L398">Pics.run_finished</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L405">Pics.run_frame</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L386">Pics.run_pure</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L395">Pics.run_remember</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L400">Pics.run_retryAt</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L402">Pics.run_retryLater</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L408">Pics.run_spawn</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/attachment/Screen.lean#L393">Pics.run_started</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/Screen.lean#L99">Raster.key_eq</a> · 2 below</li>
</ul></details>

<details><summary><b>app/community/channel/message/attachment/chunk</b> · 5</summary><ul>
<li>▫️ <a href="../app/community/channel/message/attachment/chunk/Op.lean#L27">Community.Chunk.Body.enc_tag</a> · 35 below</li>
<li>▫️ <a href="../app/community/channel/message/attachment/chunk/Op.lean#L44">Community.Chunk.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/channel/message/attachment/chunk/Op.lean#L53">Community.Chunk.byAttachment_args</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/attachment/chunk/Proofs.lean#L129">Community.attach_chunks</a> · 41 below</li>
<li>✅ <a href="../app/community/channel/message/attachment/chunk/Proofs.lean#L116">Community.chunk_own</a> · 8 below</li>
</ul></details>

<details><summary><b>app/community/channel/message/draft</b> · 6</summary><ul>
<li>▫️ <a href="../app/community/channel/message/draft/Op.lean#L36">Community.Draft.Body.enc_tag</a> · 35 below</li>
<li>▫️ <a href="../app/community/channel/message/draft/Op.lean#L52">Community.Draft.Fact.enc_tag</a> · 35 below</li>
<li>▫️ <a href="../app/community/channel/message/draft/Op.lean#L59">Community.Draft.byAcc_args</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/draft/Commands.lean#L38">Community.Draft.of_write</a> · 42 below</li>
<li>✅ <a href="../app/community/channel/message/draft/View.lean#L245">Composer.caret_clear</a> · isolated</li>
<li>✅ <a href="../app/community/channel/message/draft/View.lean#L48">Composer.pending_slot</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/channel/message/reaction</b> · 4</summary><ul>
<li>▫️ <a href="../app/community/channel/message/reaction/Op.lean#L21">Community.React.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/channel/message/reaction/Op.lean#L38">Community.React.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/channel/message/reaction/Op.lean#L47">Community.React.byMessageEmoji_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/reaction/Op.lean#L45">Community.React.byMessage_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/channel/message/receipt</b> · 7</summary><ul>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L24">Community.Receive.Body.enc_tag</a> · 23 below</li>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L72">Community.Receive.Fact.enc_tag</a> · 36 below</li>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L86">Community.Receive.all_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L82">Community.Receive.byKey_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L89">Community.Receive.byMsg_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L93">Community.Receive.childrenByKey_args</a> · isolated</li>
<li>▫️ <a href="../app/community/channel/message/receipt/Op.lean#L91">Community.Receive.rootsByKey_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/device/endpoint</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/device/endpoint/Op.lean#L19">Community.Endpoint.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/device/endpoint/Op.lean#L33">Community.Endpoint.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/device/endpoint/Op.lean#L39">Community.Endpoint.all_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/device/secret</b> · 5</summary><ul>
<li>▫️ <a href="../app/community/device/secret/Op.lean#L20">Community.Secret.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/device/secret/Op.lean#L34">Community.Secret.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/device/secret/Op.lean#L44">Community.Secret.all_args</a> · isolated</li>
<li>▫️ <a href="../app/community/device/secret/Op.lean#L40">Community.Secret.byKey_args</a> · isolated</li>
<li>✅ <a href="../app/community/device/secret/Proofs.lean#L23">Community.secret_derives</a> · 45 below</li>
</ul></details>

<details><summary><b>app/community/key</b> · 4</summary><ul>
<li>▫️ <a href="../app/community/key/Op.lean#L20">Community.ContentKey.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/key/Op.lean#L35">Community.ContentKey.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/key/Op.lean#L40">Community.ContentKey.byCommunity_args</a> · isolated</li>
<li>▫️ <a href="../app/community/key/Op.lean#L43">Community.ContentKey.byId_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/key/wrap</b> · 8</summary><ul>
<li>▫️ <a href="../app/community/key/wrap/Op.lean#L22">Community.Wrap.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/key/wrap/Op.lean#L38">Community.Wrap.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/key/wrap/Op.lean#L42">Community.Wrap.byContentKey_args</a> · isolated</li>
<li>▫️ <a href="../app/community/key/wrap/Op.lean#L45">Community.Wrap.byRecipient_args</a> · isolated</li>
<li>✅ <a href="../app/community/key/wrap/Proofs.lean#L16">Engine.View.always_eval</a> · isolated</li>
<li>✅ <a href="../app/community/key/wrap/Proofs.lean#L21">Engine.View.always_run</a> · isolated</li>
<li>▫️ <a href="../app/community/key/wrap/Proofs.lean#L44">Engine.View.bind_eq</a> · isolated</li>
<li>▫️ <a href="../app/community/key/wrap/Proofs.lean#L46">Engine.View.pure_eq</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/admin</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/member/admin/Op.lean#L19">Community.Grant.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/admin/Op.lean#L33">Community.Grant.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/admin/Op.lean#L37">Community.Grant.byUser_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/invite</b> · 4</summary><ul>
<li>▫️ <a href="../app/community/member/invite/Op.lean#L25">Community.Invitation.Body.enc_tag</a> · 26 below</li>
<li>▫️ <a href="../app/community/member/invite/Op.lean#L41">Community.Invitation.Fact.enc_tag</a> · 26 below</li>
<li>🧪 <a href="../app/community/member/invite/Proofs.lean#L126">Community.anyUser_approves_link</a> · 24 below</li>
<li>🧪 <a href="../app/community/member/invite/Proofs.lean#L147">Community.newUser_links</a> · 24 below</li>
</ul></details>

<details><summary><b>app/community/member/invite/request</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/member/invite/request/Op.lean#L24">Community.Request.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/invite/request/Op.lean#L41">Community.Request.Fact.enc_tag</a> · 26 below</li>
<li>▫️ <a href="../app/community/member/invite/request/Op.lean#L48">Community.Request.all_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/invite/request/approve</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/member/invite/request/approve/Op.lean#L21">Community.Approve.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/invite/request/approve/Op.lean#L36">Community.Approve.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/invite/request/approve/Op.lean#L40">Community.Approve.byRequest_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/invite/request/approve/admit</b> · 1</summary><ul>
<li>▫️ <a href="../app/community/member/invite/request/approve/admit/Op.lean#L21">Community.Admit.Body.enc_tag</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/join/accept</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/member/join/accept/Op.lean#L20">Community.Accept.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/join/accept/Op.lean#L34">Community.Accept.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/join/accept/Op.lean#L39">Community.Accept.all_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/join/joining</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/member/join/joining/Op.lean#L26">Community.Joining.Body.enc_tag</a> · 35 below</li>
<li>▫️ <a href="../app/community/member/join/joining/Op.lean#L45">Community.Joining.Fact.enc_tag</a> · 35 below</li>
<li>▫️ <a href="../app/community/member/join/joining/Op.lean#L50">Community.Joining.all_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/join/joining/abandon</b> · 4</summary><ul>
<li>▫️ <a href="../app/community/member/join/joining/abandon/Op.lean#L18">Community.Abandon.Body.enc_tag</a> · isolated</li>
<li>▫️ <a href="../app/community/member/join/joining/abandon/Op.lean#L33">Community.Abandon.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/join/joining/abandon/Op.lean#L40">Community.Abandon.byJoining_args</a> · isolated</li>
<li>▫️ <a href="../app/community/member/join/joining/abandon/Op.lean#L38">Community.Abandon.byRequest_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/member/remove</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/member/remove/Op.lean#L21">Community.Remove.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/remove/Op.lean#L36">Community.Remove.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/community/member/remove/Op.lean#L40">Community.Remove.byUser_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/name</b> · 3</summary><ul>
<li>▫️ <a href="../app/community/name/Op.lean#L22">Community.Rename.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/name/Op.lean#L38">Community.Rename.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/name/Op.lean#L47">Community.Rename.current_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/notice</b> · 4</summary><ul>
<li>▫️ <a href="../app/community/notice/Op.lean#L32">Community.Notice.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/notice/Op.lean#L50">Community.Notice.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/notice/Op.lean#L75">Community.Notice.Level.ofCode_code</a> · isolated</li>
<li>▫️ <a href="../app/community/notice/Op.lean#L58">Community.Notice.byRecipient_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/community/profile</b> · 5</summary><ul>
<li>▫️ <a href="../app/community/profile/Op.lean#L40">Community.Profile.Body.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/profile/Op.lean#L56">Community.Profile.Fact.enc_tag</a> · 31 below</li>
<li>▫️ <a href="../app/community/profile/Op.lean#L65">Community.Profile.all_args</a> · isolated</li>
<li>▫️ <a href="../app/community/profile/Op.lean#L68">Community.Profile.byLook_args</a> · isolated</li>
<li>▫️ <a href="../app/community/profile/Op.lean#L63">Community.Profile.byUser_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection</b> · 5</summary><ul>
<li>▫️ <a href="../app/connection/Family.lean#L380">Connection.Fact.decFrom_of</a> · 3 below</li>
<li>▫️ <a href="../app/connection/Family.lean#L371">Connection.Fact.dec_of</a> · isolated</li>
<li>▫️ <a href="../app/connection/Proofs.lean#L502">Connection.eval_liftL_pure</a> · isolated</li>
<li>✅ <a href="../app/connection/Proofs.lean#L74">Connection.intakeConn_wire</a> · 43 below</li>
<li>▫️ <a href="../app/connection/Proofs.lean#L200">Connection.run_count</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/connection</b> · 3</summary><ul>
<li>▫️ <a href="../app/connection/connection/Op.lean#L37">Connection.Reply.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/connection/Op.lean#L47">Connection.Reply.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/connection/Op.lean#L51">Connection.Reply.byRequest_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/eph</b> · 3</summary><ul>
<li>▫️ <a href="../app/connection/eph/Op.lean#L33">Connection.Eph.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/eph/Op.lean#L44">Connection.Eph.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/eph/Op.lean#L48">Connection.Eph.byOf_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/established</b> · 4</summary><ul>
<li>▫️ <a href="../app/connection/established/Op.lean#L38">Connection.Established.Body.enc_tag</a> · isolated</li>
<li>▫️ <a href="../app/connection/established/Op.lean#L53">Connection.Established.Fact.enc_tag</a> · 26 below</li>
<li>▫️ <a href="../app/connection/established/Op.lean#L57">Connection.Established.all_args</a> · isolated</li>
<li>▫️ <a href="../app/connection/established/Op.lean#L59">Connection.Established.byConn_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/given</b> · 3</summary><ul>
<li>▫️ <a href="../app/connection/given/Op.lean#L37">Connection.Given.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/given/Op.lean#L47">Connection.Given.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/given/Op.lean#L51">Connection.Given.byConn_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/opened</b> · 4</summary><ul>
<li>▫️ <a href="../app/connection/opened/Op.lean#L33">Connection.Opened.Body.enc_tag</a> · isolated</li>
<li>▫️ <a href="../app/connection/opened/Op.lean#L46">Connection.Opened.Fact.enc_tag</a> · 28 below</li>
<li>▫️ <a href="../app/connection/opened/Op.lean#L50">Connection.Opened.all_args</a> · isolated</li>
<li>▫️ <a href="../app/connection/opened/Op.lean#L52">Connection.Opened.byRequest_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/recv</b> · 3</summary><ul>
<li>▫️ <a href="../app/connection/recv/Op.lean#L36">Connection.Recv.Body.enc_tag</a> · 33 below</li>
<li>▫️ <a href="../app/connection/recv/Op.lean#L49">Connection.Recv.Fact.enc_tag</a> · 33 below</li>
<li>▫️ <a href="../app/connection/recv/Op.lean#L56">Connection.Recv.byOp_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/request</b> · 4</summary><ul>
<li>▫️ <a href="../app/connection/request/Op.lean#L51">Connection.Request.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/request/Op.lean#L62">Connection.Request.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/request/Op.lean#L68">Connection.Request.byFrm_args</a> · isolated</li>
<li>▫️ <a href="../app/connection/request/Op.lean#L66">Connection.Request.byTo_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/connection/send</b> · 3</summary><ul>
<li>▫️ <a href="../app/connection/send/Op.lean#L35">Connection.Send.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/send/Op.lean#L45">Connection.Send.Fact.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/connection/send/Op.lean#L49">Connection.Send.all_args</a> · isolated</li>
</ul></details>

<details><summary><b>app/nav</b> · 2</summary><ul>
<li>▫️ <a href="../app/nav/Op.lean#L48">Nav.all_args</a> · isolated</li>
<li>▫️ <a href="../app/nav/Proofs.lean#L57">Nav.place_kind</a> · isolated</li>
</ul></details>

<details><summary><b>app/settings/appearance</b> · 3</summary><ul>
<li>▫️ <a href="../app/settings/appearance/Op.lean#L42">Settings.Appearance.Body.enc_tag</a> · 24 below</li>
<li>▫️ <a href="../app/settings/appearance/Op.lean#L58">Settings.Appearance.all_args</a> · isolated</li>
<li>▫️ <a href="../app/settings/appearance/View.lean#L29">Settings.Appearance.pick_nil</a> · isolated</li>
</ul></details>

<details><summary><b>engine/core</b> · 113</summary><ul>
<li>✅ <a href="../engine/core/Crypto.lean#L39">Engine.Bytes.of?_none</a> · isolated</li>
<li>✅ <a href="../engine/core/CodecCost.lean#L331">Engine.Codec.cost_decBytesFromM_at</a> · 37 below</li>
<li>✅ <a href="../engine/core/Codec.lean#L868">Engine.Codec.decode_eq_fast</a> · 7 below</li>
<li>🧪 <a href="../engine/core/CodecCost.lean#L394">Engine.Codec.slow_bytes_over_budget</a> · 6 below</li>
<li>🧪 <a href="../engine/core/CodecCost.lean#L194">Engine.Codec.slow_digits_over_budget</a> · 3 below</li>
<li>▫️ <a href="../engine/core/Codec.lean#L753">Engine.Codec.tagged_enc</a> · isolated</li>
<li>✅ <a href="../engine/core/CodecCost.lean#L292">Engine.Codec.val_decBytesFromM</a> · 4 below</li>
<li>✅ <a href="../engine/core/CodecCost.lean#L121">Engine.Codec.val_decNatFromM</a> · 6 below</li>
<li>🧪 <a href="../engine/core/CodecCost.lean#L167">Engine.Codec.val_digitsSlowM</a> · isolated</li>
<li>▫️ <a href="../engine/core/CodecVia.lean#L20">Engine.Codec.via_enc</a> · isolated</li>
<li>✅ <a href="../engine/core/CodecCost.lean#L302">Engine.Codec.work_decBytesFromM</a> · 9 below</li>
<li>✅ <a href="../engine/core/CodecCost.lean#L135">Engine.Codec.work_decNatFromM</a> · 16 below</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L28">Engine.CostT.erase_bind</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L38">Engine.CostT.erase_charged</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L41">Engine.CostT.erase_chargedBy</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L44">Engine.CostT.erase_lift</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L25">Engine.CostT.erase_pure</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L23">Engine.CostT.erase_run</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L47">Engine.CostT.erase_tick</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>▫️ <a href="../engine/core/Cost.lean#L138">Engine.CostT.run_bind</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L136">Engine.CostT.run_pure</a> · isolated</li>
<li>📐 <a href="../engine/core/Cost.lean#L394">Engine.Costs.time</a> · isolated</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L60">Engine.Counted.cost_run</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>🪜 <a href="../engine/core/CostErase.lean#L56">Engine.Counted.val_erase</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>▫️ <a href="../engine/core/Cost.lean#L454">Engine.Counted.val_map</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L457">Engine.Counted.val_tick</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L88">Engine.Meter.add_comm</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L81">Engine.Meter.copied_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L68">Engine.Meter.hashed_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L78">Engine.Meter.hashed_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L67">Engine.Meter.hashes_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L77">Engine.Meter.hashes_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L65">Engine.Meter.lists_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L75">Engine.Meter.lists_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L64">Engine.Meter.reads_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L74">Engine.Meter.reads_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L73">Engine.Meter.rows_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L83">Engine.Meter.rows_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L72">Engine.Meter.seeks_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L82">Engine.Meter.seeks_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L69">Engine.Meter.spawns_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L79">Engine.Meter.spawns_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L80">Engine.Meter.work_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L66">Engine.Meter.writes_add</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L76">Engine.Meter.writes_zero</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L12">Engine.Model.run_pure</a> · isolated</li>
<li>🧪 <a href="../engine/core/WindowMutants.lean#L119">Engine.Mutants.exact_silent</a> · 158 below</li>
<li>▫️ <a href="../engine/core/WindowMutants.lean#L64">Engine.Mutants.σ_one</a> · isolated</li>
<li>▫️ <a href="../engine/core/WindowMutants.lean#L66">Engine.Mutants.σ_one_purge</a> · isolated</li>
<li>▫️ <a href="../engine/core/Core.lean#L51">Engine.Op.make_body</a> · isolated</li>
<li>▫️ <a href="../engine/core/Core.lean#L49">Engine.Op.make_kind</a> · isolated</li>
<li>▫️ <a href="../engine/core/Core.lean#L50">Engine.Op.make_reqs</a> · isolated</li>
<li>▫️ <a href="../engine/core/WindowIndex.lean#L44">Engine.Pos.lt_of_le_lt</a> · 19 below</li>
<li>▫️ <a href="../engine/core/Decl.lean#L34">Engine.Rel.comap_args</a> · isolated</li>
<li>▫️ <a href="../engine/core/View.lean#L60">Engine.View.eval_pure</a> · isolated</li>
<li>▫️ <a href="../engine/core/View.lean#L71">Engine.View.eval_read</a> · isolated</li>
<li>▫️ <a href="../engine/core/ListCost.lean#L90">Engine.View.listsAt_read</a> · isolated</li>
<li>✅ <a href="../engine/core/ListCost.lean#L102">Engine.View.view_lists</a> · 5 below</li>
<li>▫️ <a href="../engine/core/Cost.lean#L406">Engine.costs_lift</a> · 2 below</li>
<li>✅ <a href="../engine/core/Query.lean#L756">Engine.countWith_split</a> · isolated</li>
<li>🪜 <a href="../engine/core/IngestCost.lean#L196">Engine.cr_erase</a> · a step of Engine.Codec.cost_decBytesFromM_at, Engine.Codec.val_decBytesFromM, Engine.Codec.val_decNatFromM +18</li>
<li>▫️ <a href="../engine/core/IngestCost.lean#L202">Engine.cr_pure_meter</a> · isolated</li>
<li>▫️ <a href="../engine/core/Left.lean#L158">Engine.eval_liftR_list</a> · isolated</li>
<li>✅ <a href="../engine/core/Union.lean#L233">Engine.eval_strict</a> · 24 below</li>
<li>✅ <a href="../engine/core/IngestCost.lean#L303">Engine.fed_reqs</a> · 14 below</li>
<li>📐 <a href="../engine/core/Query.lean#L673">Engine.id_bind</a> · isolated</li>
<li>✅ <a href="../engine/core/Query.lean#L312">Engine.inRange_unbounded</a> · isolated</li>
<li>✅ <a href="../engine/core/IngestCost.lean#L49">Engine.ingest_costs</a> · 12 below</li>
<li>✅ <a href="../engine/core/Sync.lean#L99">Engine.intakeConn_reqs</a> · isolated</li>
<li>✅ <a href="../engine/core/Sync.lean#L93">Engine.intake_mine</a> · isolated</li>
<li>✅ <a href="../engine/core/Left.lean#L104">Engine.left_status</a> · 26 below</li>
<li>✅ <a href="../engine/core/Query.lean#L750">Engine.listPlan_split</a> · isolated</li>
<li>📐 <a href="../engine/core/ListCost.lean#L34">Engine.list_costs</a> · 12 below</li>
<li>📐 <a href="../engine/core/ListCost.lean#L63">Engine.model_fits</a> · 1 below</li>
<li>✅ <a href="../engine/core/Query.lean#L401">Engine.pickMin_le</a> · isolated</li>
<li>✅ <a href="../engine/core/Project.lean#L257">Engine.proj_unique</a> · 34 below</li>
<li>▫️ <a href="../engine/core/Run.lean#L22">Engine.run_addWait</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L26">Engine.run_clearWaiters</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L40">Engine.run_countOps</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L38">Engine.run_deleteOp</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L34">Engine.run_dependents</a> · isolated</li>
<li>✅ <a href="../engine/core/Run.lean#L156">Engine.run_drain</a> · 8 below</li>
<li>▫️ <a href="../engine/core/Run.lean#L18">Engine.run_getStatus</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L30">Engine.run_index</a> · isolated</li>
<li>▫️ <a href="../engine/core/Query.lean#L776">Engine.run_list</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L32">Engine.run_lookup</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L28">Engine.run_push</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L16">Engine.run_putOp</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L20">Engine.run_setStatus</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L36">Engine.run_undecide</a> · isolated</li>
<li>▫️ <a href="../engine/core/Run.lean#L24">Engine.run_waiters</a> · isolated</li>
<li>✅ <a href="../engine/core/IngestCost.lean#L162">Engine.step_capped</a> · 22 below</li>
<li>✅ <a href="../engine/core/IngestCost.lean#L309">Engine.step_reads_fed</a> · 42 below</li>
<li>▫️ <a href="../engine/core/Cost.lean#L264">Engine.withinP_charged</a> · 1 below</li>
<li>▫️ <a href="../engine/core/Cost.lean#L289">Engine.within_bindP_le</a> · 2 below</li>
<li>▫️ <a href="../engine/core/CostStore.lean#L120">Engine.within_getOp</a> · 1 below</li>
<li>▫️ <a href="../engine/core/CostStore.lean#L123">Engine.within_getStatus</a> · 1 below</li>
<li>▫️ <a href="../engine/core/Cost.lean#L230">Engine.within_ite</a> · isolated</li>
<li>▫️ <a href="../engine/core/Cost.lean#L203">Engine.within_lift</a> · 1 below</li>
<li>✅ <a href="../engine/core/Merkle.lean#L457">Merkle.encode_verify</a> · 11 below</li>
<li>✅ <a href="../engine/core/MerkleCost.lean#L224">Merkle.rootAndProofs_hashed_lt</a> · 41 below</li>
<li>✅ <a href="../engine/core/MerkleCost.lean#L113">Merkle.rootAndProofs_hashes_lt</a> · 24 below</li>
<li>🧪 <a href="../engine/core/MerkleCost.lean#L353">Merkle.slow_over_budget</a> · 12 below</li>
<li>▫️ <a href="../engine/core/MerkleCost.lean#L29">Merkle.val_hashM</a> · isolated</li>
<li>✅ <a href="../engine/core/MerkleCost.lean#L54">Merkle.val_rootAndProofsM</a> · 25 below</li>
<li>🧪 <a href="../engine/core/MerkleCost.lean#L309">Merkle.val_rootAndProofsSlowM</a> · 10 below</li>
<li>▫️ <a href="../engine/core/FIFO.lean#L82">Net.FIFO.fair_loss</a> · 3 below</li>
<li>▫️ <a href="../engine/core/SqliteLaws.lean#L37">Trust.model_pure</a> · isolated</li>
<li>✅ <a href="../engine/core/SqliteLaws.lean#L254">Trust.receive_shows_model</a> · 54 below</li>
<li>▫️ <a href="../engine/core/SqliteLaws.lean#L50">Trust.sql_earlyReturn</a> · isolated</li>
<li>▫️ <a href="../engine/core/SqliteLaws.lean#L45">Trust.sql_getDb</a> · isolated</li>
<li>▫️ <a href="../engine/core/SqliteLaws.lean#L42">Trust.sql_liftM</a> · isolated</li>
<li>▫️ <a href="../engine/core/SqliteLaws.lean#L39">Trust.sql_tryCatch</a> · isolated</li>
</ul></details>

<details><summary><b>engine/renderer</b> · 132</summary><ul>
<li>✅ <a href="../engine/renderer/Contrast.lean#L50">Contrast.channel_bounds</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Contrast.lean#L111">Contrast.possible</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/Cover.lean#L122">Cover.painted_no_hold</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/Cue.lean#L22">Cue.nonempty</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Cue.lean#L30">Cue.same</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L118">Demand.background_paused</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L107">Demand.complete_current</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L235">Demand.empty_before_next</a> · isolated</li>
<li>✅ <a href="../engine/renderer/DemandRank.lean#L212">Demand.first_on_time</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L54">Demand.heldIndex_agrees</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L122">Demand.idle_fifo</a> · isolated</li>
<li>✅ <a href="../engine/renderer/DemandRank.lean#L169">Demand.mem_reconcileFirst</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L238">Demand.reconcile_before_next</a> · 4 below</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L111">Demand.reconcile_empty</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L167">Demand.reconcile_members</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L136">Demand.unmounted</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L139">Demand.unmounted_ticket</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L114">Demand.visible_first</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Demand.lean#L129">Demand.visible_owner_holds</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L132">Input.classified_key</a> · 5 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L121">Input.classified_page</a> · 3 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L143">Input.delivered_page</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L65">Input.deterministic</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/InputLaws.lean#L41">Input.early_tick</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L28">Input.extra_down</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L25">Input.first_pointer</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L33">Input.other_pointer</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L50">Input.release_event</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L19">Input.release_moved</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L60">Input.revoked_release</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L71">Input.sequence_offset</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L88">Input.tap_content</a> · isolated</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L93">Input.tap_page</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/InputLaws.lean#L164">Input.witnesses</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Label.lean#L21">Label.copy_exact</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Label.lean#L23">Label.line_reachable</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/BoardLaws.lean#L202">Live.Board.Run.next_le</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/BoardLaws.lean#L182">Live.Board.Step.fresh</a> · 6 below</li>
<li>▫️ <a href="../engine/renderer/BoardLaws.lean#L152">Live.Board.fresh_empty</a> · isolated</li>
<li>✅ <a href="../engine/renderer/BoardLaws.lean#L48">Live.Board.put_same</a> · isolated</li>
<li>✅ <a href="../engine/renderer/BoardLaws.lean#L217">Live.Board.ver_ident</a> · 9 below</li>
<li>🧪 <a href="../engine/renderer/ActsLaws.lean#L319">Live.Eager.acts_fresh</a> · 52 below</li>
<li>🧪 <a href="../engine/renderer/ReaderLaws.lean#L601">Live.Eager.eager_stale</a> · 14 below</li>
<li>🧪 <a href="../engine/renderer/ActsLaws.lean#L306">Live.Eager.late_stale</a> · 1 below</li>
<li>🧪 <a href="../engine/renderer/ReaderLaws.lean#L612">Live.Eager.marked_fresh</a> · 33 below</li>
<li>🧪 <a href="../engine/renderer/BoardLaws.lean#L530">Live.Gated.gated_stale</a> · isolated</li>
<li>🧪 <a href="../engine/renderer/BoardLaws.lean#L544">Live.Gated.ungated_fresh</a> · 19 below</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L294">Live.RWorld.counter_idle</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L281">Live.RWorld.countok_commit</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L289">Live.RWorld.countok_frame</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L284">Live.RWorld.countok_passIdx</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L279">Live.RWorld.countok_start</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L358">Live.RWorld.idxok_frame</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L392">Live.RWorld.idxok_passIdx</a> · 15 below</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L239">Live.RWorld.idxok_start</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L360">Live.RWorld.idxok_want</a> · 2 below</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L310">Live.RWorld.inv_passIdx</a> · 29 below</li>
<li>▫️ <a href="../engine/renderer/ReaderLaws.lean#L235">Live.RWorld.inv_start</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/ReaderLaws.lean#L260">Live.RWorld.inv_want</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/ActsLaws.lean#L139">Live.RWorld.passIdx_wants</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/ReaderLaws.lean#L328">Live.RWorld.pass_store</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L268">Live.RWorld.rest_idle</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L321">Live.RWorld.settle_idx</a> · 33 below</li>
<li>▫️ <a href="../engine/renderer/BoardLaws.lean#L404">Live.World.inv_want</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/BoardLaws.lean#L494">Live.World.pass_comp</a> · isolated</li>
<li>✅ <a href="../engine/renderer/ActsLaws.lean#L30">Live.acts_force</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L170">Live.always_moves</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/ActsLaws.lean#L48">Live.contains_actsFirst</a> · 1 below</li>
<li>▫️ <a href="../engine/renderer/ReaderLaws.lean#L133">Live.markM_cost</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L162">Live.nextGen_moves</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L159">Live.nextGen_same</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L195">Live.passCostM_cost</a> · 8 below</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L189">Live.poll_queries</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/ActsLaws.lean#L36">Live.rest_ignores_acts</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L121">Live.scanM_cost</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/RestLaws.lean#L182">Live.start_rest</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Nav.lean#L105">Nav.back_reset</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Nav.lean#L135">Nav.swap_inv</a> · 3 below</li>
<li>✅ <a href="../engine/renderer/Occlusion.lean#L64">Occlusion.modal_inert</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Occlusion.lean#L45">Occlusion.placed_table</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Overlay.lean#L16">Overlay.edge_contrast</a> · 7 below</li>
<li>✅ <a href="../engine/renderer/Photo.lean#L27">Photo.inactive_rejects</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Photo.lean#L34">Photo.other_owner_rejects</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Photo.lean#L30">Photo.stale_rejects</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Safe.lean#L77">Safe.content_inside</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Safe.lean#L89">Safe.target_safe</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/Safe.lean#L97">Safe.target_witness</a> · isolated</li>
<li>✅ <a href="../engine/renderer/SafeFrame.lean#L70">SafeFrame.band_colour</a> · isolated</li>
<li>✅ <a href="../engine/renderer/SafeFrame.lean#L41">SafeFrame.target_minimum</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Scrim.lean#L47">Scrim.legible</a> · 5 below</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L78">Scrollbar.exact</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L57">Scrollbar.fits</a> · 2 below</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L73">Scrollbar.monotone</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L62">Scrollbar.newest_bottom</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L65">Scrollbar.oldest_top</a> · 1 below</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L239">Scrollbar.ranks_fit</a> · 8 below</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L248">Scrollbar.ranks_mono</a> · 4 below</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L252">Scrollbar.ranks_newest</a> · 4 below</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L88">Scrollbar.seek_below</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/Scrollbar.lean#L98">Scrollbar.seek_mono</a> · isolated</li>
<li>✅ <a href="../engine/renderer/SheetGeom.lean#L186">SheetGeom.clamp_le</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/SheetGeom.lean#L216">SheetGeom.compose_size</a> · isolated</li>
<li>✅ <a href="../engine/renderer/SlideLaws.lean#L165">Slide.delta_eq</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/SlideLaws.lean#L181">Slide.fillRow_eq</a> · 6 below</li>
<li>✅ <a href="../engine/renderer/SlideLaws.lean#L199">Slide.pick_eq</a> · 8 below</li>
<li>✅ <a href="../engine/renderer/Surface.lean#L80">Surface.composer_top</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Surface.lean#L103">Surface.published_composer</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Surface.lean#L85">Surface.published_row</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/TextLaws.lean#L103">Text.arabic_numbers_witness</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Text.lean#L275">Text.metricWidth_fits</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TextLaws.lean#L98">Text.numbers_witness</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Text.lean#L294">Text.pixelLine_glyphs</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Theme.lean#L36">Theme.follows</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Theme.lean#L39">Theme.forced</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Theme.lean#L43">Theme.roundtrip</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L65">Toast.dismissed</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L62">Toast.expired</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L30">Toast.placed_safe</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L51">Toast.placed_size</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L38">Toast.placed_view</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L70">Toast.placed_witness</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Toast.lean#L67">Toast.raised_visible</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L28">Translate.copied_row</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L156">Translate.delta_value</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L112">Translate.edge_fill</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L104">Translate.edge_list</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L94">Translate.line_painted</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L76">Translate.outside</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L17">Translate.pinned</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L66">Translate.source_content</a> · 2 below</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L166">Translate.tap_content</a> · isolated</li>
<li>✅ <a href="../engine/renderer/TranslateLaws.lean#L170">Translate.witnesses</a> · isolated</li>
</ul></details>

<details><summary><b>engine/renderer/Ttf</b> · 7</summary><ul>
<li>🧪 <a href="../engine/renderer/Ttf/Memo.lean#L126">Ttf.Memo.shifted_not_exact</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Ttf/Laws.lean#L32">Ttf.cmap12_glyph</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Ttf/Laws.lean#L38">Ttf.cmap4_array</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Ttf/Laws.lean#L35">Ttf.cmap4_delta</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Ttf/Laws.lean#L50">Ttf.coverage_bound</a> · 1 below</li>
<li>✅ <a href="../engine/renderer/Ttf/Laws.lean#L84">Ttf.ink_witness</a> · isolated</li>
<li>✅ <a href="../engine/renderer/Ttf/Laws.lean#L28">Ttf.lookup_singleton</a> · isolated</li>
</ul></details>

<details><summary><b>engine/renderer/qr</b> · 5</summary><ul>
<li>▫️ <a href="../engine/renderer/qr/SegLaws.lean#L15">Qr.bitsOf_succ</a> · isolated</li>
<li>✅ <a href="../engine/renderer/qr/Laws.lean#L81">Qr.decodeImage_malformed</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/qr/SegLaws.lean#L215">Qr.dig_lt</a> · 2 below</li>
<li>▫️ <a href="../engine/renderer/qr/Bits.lean#L129">Qr.readBits_none_of_length</a> · isolated</li>
<li>▫️ <a href="../engine/renderer/qr/Bits.lean#L97">Qr.readBits_short</a> · isolated</li>
</ul></details>

<details><summary><b>engine/sync</b> · 58</summary><ul>
<li>▫️ <a href="../engine/sync/Conn.lean#L625">Engine.Sync.Conn.ask_take</a> · isolated</li>
<li>▫️ <a href="../engine/sync/Conn.lean#L683">Engine.Sync.Conn.onAsk_dialer</a> · 1 below</li>
<li>▫️ <a href="../engine/sync/Conn.lean#L679">Engine.Sync.Conn.onAsk_given</a> · 1 below</li>
<li>▫️ <a href="../engine/sync/Conn.lean#L673">Engine.Sync.Conn.onAsk_heard</a> · 1 below</li>
<li>▫️ <a href="../engine/sync/Conn.lean#L677">Engine.Sync.Conn.onAsk_sent</a> · 1 below</li>
<li>▫️ <a href="../engine/sync/Walk.lean#L44">Engine.Sync.Near.mono</a> · isolated</li>
<li>▫️ <a href="../engine/sync/Walk.lean#L49">Engine.Sync.Near.of_none</a> · isolated</li>
<li>▫️ <a href="../engine/sync/Conn.lean#L237">Engine.Sync.RoomTree.ofList_items</a> · 68 below</li>
<li>▫️ <a href="../engine/sync/Conn.lean#L175">Engine.Sync.RoomTree.sorted_filter</a> · 1 below</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L490">Engine.Sync.RoundRun.advance_eq</a> · isolated</li>
<li>▫️ <a href="../engine/sync/RoundRun.lean#L502">Engine.Sync.RoundRun.exec_full</a> · 2 below</li>
<li>📐 <a href="../engine/sync/RoundRun.lean#L616">Engine.Sync.RoundRun.execute_runs</a> · isolated</li>
<li>📐 <a href="../engine/sync/RoundRun.lean#L713">Engine.Sync.RoundRun.initial_asks</a> · isolated</li>
<li>📐 <a href="../engine/sync/RoundRun.lean#L704">Engine.Sync.RoundRun.initial_claim</a> · 88 below</li>
<li>📐 <a href="../engine/sync/RoundRun.lean#L696">Engine.Sync.RoundRun.initial_ready</a> · isolated</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L176">Engine.Sync.RoundRun.items_eq</a> · isolated</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L170">Engine.Sync.RoundRun.items_full</a> · 2 below</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L137">Engine.Sync.RoundRun.result_eq</a> · isolated</li>
<li>📐 <a href="../engine/sync/RoundRun.lean#L674">Engine.Sync.RoundRun.sound_of_check</a> · 3 below</li>
<li>▫️ <a href="../engine/sync/SimLaws.lean#L59">Engine.Sync.Sim.getStatus'</a> · isolated</li>
<li>▫️ <a href="../engine/sync/SimLaws.lean#L63">Engine.Sync.Sim.list'</a> · isolated</li>
<li>✅ <a href="../engine/sync/SweepLaws.lean#L99">Engine.Sync.Sweep.retried</a> · 3 below</li>
<li>▫️ <a href="../engine/sync/RetryLaws.lean#L19">Engine.Sync.asked_full</a> · isolated</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L66">Engine.Sync.beginRound_not_newer</a> · isolated</li>
<li>▫️ <a href="../engine/sync/WindowLaws.lean#L58">Engine.Sync.byId_foldl_other</a> · 2 below</li>
<li>✅ <a href="../engine/sync/ClaimsLaws.lean#L288">Engine.Sync.claims_log</a> · 47 below</li>
<li>✅ <a href="../engine/sync/SessionLaws.lean#L134">Engine.Sync.closed_terminal</a> · 23 below</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L58">Engine.Sync.conn_ignores_old_round</a> · 2 below</li>
<li>✅ <a href="../engine/sync/EventLaws.lean#L42">Engine.Sync.due_iff</a> · isolated</li>
<li>▫️ <a href="../engine/sync/DepthLaws.lean#L51">Engine.Sync.ends_exchange</a> · 1 below</li>
<li>▫️ <a href="../engine/sync/ServeLaws.lean#L210">Engine.Sync.fetch_reads</a> · 2 below</li>
<li>✅ <a href="../engine/sync/BoundsLaws.lean#L197">Engine.Sync.filedGive_reachable</a> · isolated</li>
<li>▫️ <a href="../engine/sync/OfferLaws.lean#L257">Engine.Sync.filterMapM_getOp</a> · 2 below</li>
<li>✅ <a href="../engine/sync/Treap.lean#L135">Engine.Sync.height_canon</a> · 31 below</li>
<li>✅ <a href="../engine/sync/SessionLaws.lean#L94">Engine.Sync.hello_answered</a> · 44 below</li>
<li>✅ <a href="../engine/sync/RetryLaws.lean#L129">Engine.Sync.honest_no_drop_runs</a> · 5 below</li>
<li>✅ <a href="../engine/sync/TimeLaws.lean#L114">Engine.Sync.keepalive_runs</a> · 2 below</li>
<li>✅ <a href="../engine/sync/RetryLaws.lean#L14">Engine.Sync.known_forgets</a> · isolated</li>
<li>✅ <a href="../engine/sync/Fp.lean#L407">Engine.Sync.lbl_perm</a> · 37 below</li>
<li>✅ <a href="../engine/sync/RoundRun.lean#L72">Engine.Sync.noteEpoch_bounded</a> · isolated</li>
<li>▫️ <a href="../engine/sync/ServeLaws.lean#L342">Engine.Sync.onWant_drop</a> · isolated</li>
<li>✅ <a href="../engine/sync/OfferLaws.lean#L460">Engine.Sync.open_keeps</a> · isolated</li>
<li>✅ <a href="../engine/sync/SessionLaws.lean#L141">Engine.Sync.open_session</a> · isolated</li>
<li>▫️ <a href="../engine/sync/WindowLaws.lean#L162">Engine.Sync.over_sorted</a> · isolated</li>
<li>▫️ <a href="../engine/sync/ClaimsLaws.lean#L165">Engine.Sync.picks_sublist</a> · isolated</li>
<li>✅ <a href="../engine/sync/ClosureStore.lean#L14">Engine.Sync.recv_data_takes</a> · 35 below</li>
<li>▫️ <a href="../engine/sync/RetryLaws.lean#L168">Engine.Sync.retried_holds</a> · 41 below</li>
<li>▫️ <a href="../engine/sync/RetryLaws.lean#L206">Engine.Sync.retry_bounded</a> · 48 below</li>
<li>✅ <a href="../engine/sync/EventLaws.lean#L99">Engine.Sync.roundedAt_note</a> · isolated</li>
<li>▫️ <a href="../engine/sync/SimLaws.lean#L202">Engine.Sync.serveOwed_held</a> · 7 below</li>
<li>✅ <a href="../engine/sync/ServeLaws.lean#L397">Engine.Sync.serveOwed_hot_count</a> · 6 below</li>
<li>✅ <a href="../engine/sync/ConnLaws.lean#L116">Engine.Sync.serveOwed_send</a> · 7 below</li>
<li>▫️ <a href="../engine/sync/ServeLaws.lean#L29">Engine.Sync.serve_nil</a> · isolated</li>
<li>✅ <a href="../engine/sync/ServeLaws.lean#L57">Engine.Sync.serve_reads</a> · 3 below</li>
<li>✅ <a href="../engine/sync/SessionLaws.lean#L145">Engine.Sync.session_runs</a> · 44 below</li>
<li>✅ <a href="../engine/sync/BoundsLaws.lean#L202">Engine.Sync.tickGive_reachable</a> · isolated</li>
<li>✅ <a href="../engine/sync/WindowLaws.lean#L294">Engine.Sync.window_covers</a> · 2 below</li>
<li>✅ <a href="../engine/sync/ClosureStore.lean#L210">Engine.Sync.write_log_subset</a> · 7 below</li>
</ul></details>

<details><summary><b>engine/wire</b> · 86</summary><ul>
<li>🧪 <a href="../engine/wire/NoiseSymbolic.lean#L976">Connection.Noise.Symbolic.read1Slip_forged</a> · 1 below</li>
<li>▫️ <a href="../engine/wire/Noise.lean#L242">Connection.Noise.split_valid</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L85">Engine.Sync.Acts.append_def</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L88">Engine.Sync.Acts.empty_append</a> · isolated</li>
<li>✅ <a href="../engine/wire/DialQueue.lean#L40">Engine.Sync.DialQueue.enqueue_bounded</a> · isolated</li>
<li>✅ <a href="../engine/wire/DialQueue.lean#L29">Engine.Sync.DialQueue.enqueue_pending</a> · 1 below</li>
<li>✅ <a href="../engine/wire/DialQueue.lean#L84">Engine.Sync.DialQueue.reserve_bounded</a> · 1 below</li>
<li>✅ <a href="../engine/wire/DialQueue.lean#L51">Engine.Sync.DialQueue.reserve_head</a> · isolated</li>
<li>✅ <a href="../engine/wire/DialQueue.lean#L57">Engine.Sync.DialQueue.reserve_mem</a> · isolated</li>
<li>✅ <a href="../engine/wire/DialQueue.lean#L72">Engine.Sync.DialQueue.reserve_order</a> · isolated</li>
<li>▫️ <a href="../engine/wire/EgressLaws.lean#L81">Engine.Sync.Goes.getStatus'</a> · 3 below</li>
<li>▫️ <a href="../engine/wire/EgressLaws.lean#L85">Engine.Sync.Goes.purge'</a> · 1 below</li>
<li>▫️ <a href="../engine/wire/NodeLaws.lean#L30">Engine.Sync.HeldM.getStatus_apply</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L66">Engine.Sync.HeldM.pure_bind</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L67">Engine.Sync.HeldM.run_getOp</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L69">Engine.Sync.HeldM.run_getStatus</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L65">Engine.Sync.HeldM.run_pure</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L77">Engine.Sync.HeldM.run_turn</a> · isolated</li>
<li>✅ <a href="../engine/wire/IngressLaws.lean#L56">Engine.Sync.Ingress.scan_selected</a> · isolated</li>
<li>✅ <a href="../engine/wire/LoopLaws.lean#L20">Engine.Sync.Node.step_close</a> · isolated</li>
<li>✅ <a href="../engine/wire/LoopLaws.lean#L15">Engine.Sync.Node.step_frame</a> · isolated</li>
<li>✅ <a href="../engine/wire/LoopLaws.lean#L18">Engine.Sync.Node.step_tick</a> · isolated</li>
<li>✅ <a href="../engine/wire/LoopLaws.lean#L12">Engine.Sync.Node.step_write</a> · isolated</li>
<li>▫️ <a href="../engine/wire/NodeUniqueLaws.lean#L257">Engine.Sync.NodeUnique.sent_shape</a> · isolated</li>
<li>✅ <a href="../engine/wire/OutboxLaws.lean#L84">Engine.Sync.Outbox.drain_lingers</a> · isolated</li>
<li>✅ <a href="../engine/wire/OutboxLaws.lean#L90">Engine.Sync.Outbox.drain_quiet_closes</a> · isolated</li>
<li>▫️ <a href="../engine/wire/OutboxLaws.lean#L14">Engine.Sync.Outbox.empty_bounded</a> · isolated</li>
<li>✅ <a href="../engine/wire/OutboxLaws.lean#L94">Engine.Sync.Outbox.stopped_never_lingers</a> · isolated</li>
<li>✅ <a href="../engine/wire/Reserved.lean#L245">Engine.Sync.Reserved.normal_flood_does_not_starve_retry</a> · 1 below</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L183">Engine.Sync.Reserved.queued_bytes_bounded</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L240">Engine.Sync.Reserved.queued_marked_inflight</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L236">Engine.Sync.Reserved.queued_next_batch</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L135">Engine.Sync.Reserved.rejected_push_preserves</a> · isolated</li>
<li>📐 <a href="../engine/wire/RetryOrderLaws.lean#L214">Engine.Sync.RetryOrder.Run.nodup</a> · 3 below</li>
<li>✅ <a href="../engine/wire/RetryOrderLaws.lean#L17">Engine.Sync.RetryOrder.claim_busy</a> · isolated</li>
<li>✅ <a href="../engine/wire/RetryOrderLaws.lean#L56">Engine.Sync.RetryOrder.offered_length</a> · 1 below</li>
<li>✅ <a href="../engine/wire/RetryOrderLaws.lean#L62">Engine.Sync.RetryOrder.offered_none</a> · isolated</li>
<li>✅ <a href="../engine/wire/RetryOrderLaws.lean#L71">Engine.Sync.RetryOrder.reconcile_prefix</a> · isolated</li>
<li>✅ <a href="../engine/wire/RetryOrderLaws.lean#L22">Engine.Sync.RetryOrder.scan_append</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L72">Engine.Sync.RetrySlot.cannot_refill_during_write</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L57">Engine.Sync.RetrySlot.offer_busy</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L75">Engine.Sync.RetrySlot.successful_write_waits_for_ack</a> · isolated</li>
<li>▫️ <a href="../engine/wire/Reserved.lean#L69">Engine.Sync.RetrySlot.take_queued</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L433">Engine.Sync.Tick.waiting</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L791">Engine.Sync.World.run_net</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L465">Engine.Sync.bundles_one</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L72">Engine.Sync.cut_progress</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L260">Engine.Sync.frame_next</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L241">Engine.Sync.framesFor_mem</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L246">Engine.Sync.framesFor_only</a> · isolated</li>
<li>✅ <a href="../engine/wire/Frame.lean#L200">Engine.Sync.frames_frame</a> · 4 below</li>
<li>✅ <a href="../engine/wire/Frame.lean#L189">Engine.Sync.frames_size</a> · 2 below</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L523">Engine.Sync.heat_addrs</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L521">Engine.Sync.heat_conns</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L526">Engine.Sync.heat_dropped</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L527">Engine.Sync.heat_floor</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L525">Engine.Sync.heat_fresh</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L524">Engine.Sync.heat_ix</a> · isolated</li>
<li>▫️ <a href="../engine/wire/NodeLaws.lean#L189">Engine.Sync.items_foldl</a> · 70 below</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L518">Engine.Sync.lane_hold_one</a> · 2 below</li>
<li>✅ <a href="../engine/wire/NodeLaws.lean#L62">Engine.Sync.onSealed_none</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L137">Engine.Sync.push_over</a> · isolated</li>
<li>✅ <a href="../engine/wire/WorldLaws.lean#L45">Engine.Sync.remember_fits</a> · 1 below</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L215">Engine.Sync.room_window</a> · 1 below</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L363">Engine.Sync.sealRetries_nil</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LaneLaws.lean#L531">Engine.Sync.sends_serve</a> · isolated</li>
<li>▫️ <a href="../engine/wire/EgressLaws.lean#L164">Engine.Sync.sent_afterActs</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L233">Engine.Sync.shut_live</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L535">Engine.Sync.split_urgent</a> · isolated</li>
<li>✅ <a href="../engine/wire/LaneLaws.lean#L227">Engine.Sync.stall_closes</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L257">Engine.Sync.sync_cfg</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L266">Engine.Sync.sync_closing</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L269">Engine.Sync.sync_dial</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L270">Engine.Sync.sync_established</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L256">Engine.Sync.sync_fam</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L264">Engine.Sync.sync_onGiven</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L258">Engine.Sync.sync_openFrame</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L265">Engine.Sync.sync_outbox</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L268">Engine.Sync.sync_react</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L262">Engine.Sync.sync_recv</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L267">Engine.Sync.sync_retired</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L261">Engine.Sync.sync_rooms</a> · isolated</li>
<li>▫️ <a href="../engine/wire/WorldLaws.lean#L259">Engine.Sync.sync_sealFor</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LoopLaws.lean#L27">Engine.Sync.Loop.run_bind</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LoopLaws.lean#L30">Engine.Sync.Loop.run_map</a> · isolated</li>
<li>▫️ <a href="../engine/wire/LoopLaws.lean#L33">Engine.Sync.Loop.run_pure</a> · isolated</li>
</ul></details>

<details><summary><b>engine/wire/mdns</b> · 5</summary><ul>
<li>▫️ <a href="../engine/wire/mdns/Laws.lean#L86">Mdns.be16_length</a> · isolated</li>
<li>▫️ <a href="../engine/wire/mdns/Laws.lean#L87">Mdns.be32_length</a> · isolated</li>
<li>▫️ <a href="../engine/wire/mdns/Laws.lean#L195">Mdns.u16_toNat_toUInt16</a> · isolated</li>
<li>▫️ <a href="../engine/wire/mdns/Laws.lean#L108">Mdns.u32_lt</a> · 2 below</li>
<li>▫️ <a href="../engine/wire/mdns/Laws.lean#L196">Mdns.u32_toNat_toUInt32</a> · isolated</li>
</ul></details>

<details><summary><b>engine/world</b> · 17</summary><ul>
<li>▫️ <a href="../engine/world/Good.lean#L148">Engine.World.Keeps.and</a> · isolated</li>
<li>▫️ <a href="../engine/world/Good.lean#L139">Engine.World.Local.and</a> · isolated</li>
<li>▫️ <a href="../engine/world/Pieces.lean#L67">Engine.World.MetaOnly.bind'</a> · isolated</li>
<li>▫️ <a href="../engine/world/Pieces.lean#L64">Engine.World.MetaOnly.pure'</a> · isolated</li>
<li>▫️ <a href="../engine/world/Pieces.lean#L290">Engine.World.Next.call</a> · isolated</li>
<li>▫️ <a href="../engine/world/InvIx.lean#L489">Engine.World.Plain.ix_covers</a> · 183 below</li>
<li>▫️ <a href="../engine/world/InvIx.lean#L478">Engine.World.Plain.owes_queued</a> · 144 below</li>
<li>▫️ <a href="../engine/world/Inv.lean#L70">Engine.World.Plain.reads_meta</a> · isolated</li>
<li>▫️ <a href="../engine/world/Drain.lean#L42">Engine.World.Waits.mono</a> · isolated</li>
<li>▫️ <a href="../engine/world/Asks.lean#L95">Engine.World.admitAsks_sub</a> · 1 below</li>
<li>▫️ <a href="../engine/world/Epidemic.lean#L239">Engine.World.chain_of</a> · 11 below</li>
<li>▫️ <a href="../engine/world/Epidemic.lean#L219">Engine.World.converge_all</a> · 9 below</li>
<li>▫️ <a href="../engine/world/Epidemic.lean#L229">Engine.World.converge_three</a> · 13 below</li>
<li>▫️ <a href="../engine/world/Asks.lean#L322">Engine.World.filedStep_asked</a> · isolated</li>
<li>▫️ <a href="../engine/world/Asks.lean#L360">Engine.World.filed_asked</a> · 3 below</li>
<li>▫️ <a href="../engine/world/Epidemic.lean#L246">Engine.World.star_of</a> · 9 below</li>
<li>▫️ <a href="../engine/world/Epidemic.lean#L253">Engine.World.web_of</a> · 5 below</li>
</ul></details>
