# Security proofs › Connections

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Security proofs › Connections**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1394) · 🌐 world: the node's code in a World (72) · 🪜 step: a step of a wired law (59) · 📐 model: over a model (73) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2258)

<ul>
<li><details><summary><a id="law-Connection.opened_endpoint"></a>✅ <a href="../../app/Proofs.lean#L395">Connection.opened_endpoint</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/opened/Proofs.lean#L14">Connection.check_opened</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.established_endpoint"></a>✅ <a href="../../app/Proofs.lean#L424">Connection.established_endpoint</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/established/Proofs.lean#L14">Connection.check_established</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.endpoint_signed"></a>✅ <a href="../../app/community/member/invite/request/Proofs.lean#L69">Community.endpoint_signed</a> · 47 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.check_admission">Community.check_admission</a> ↪ · 24 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.check_request">Community.check_request</a> ↪ · 24 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1319">Community.all2_cons2</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.endpoint_derives"></a>✅ <a href="../../app/community/device/endpoint/Proofs.lean#L31">Community.endpoint_derives</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/device/endpoint/Proofs.lean#L16">Community.check_endpoint</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.meV_node"></a>✅ <a href="../../app/connection/Proofs.lean#L258">Connection.meV_node</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.new_device_trusted"></a>✅ <a href="../../app/community/Proofs.lean#L951">Community.new_device_trusted</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_iff"></a>✅ <a href="../../app/community/Proofs.lean#L838">Community.connect_iff</a> · 68 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.live_iff">Community.live_iff</a> ↪ · 66 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1692">Community.byKey_args</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.deviceLive_iff"></a>✅ <a href="../../app/community/Proofs.lean#L728">Community.deviceLive_iff</a> · 62 below</summary><ul>
<li>✅ <a href="#law-Community.removals_iff">Community.removals_iff</a> ↪ · 55 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li><details><summary><a id="law-Community.unremoved_iff"></a>✅ <a href="../../app/community/Proofs.lean#L685">Community.unremoved_iff</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Proofs.lean#L672">Community.mem_cons_row</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1651">Community.byDevice_args</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.refuse_nonmember"></a>✅ <a href="../../app/community/Proofs.lean#L851">Community.refuse_nonmember</a> · 70 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L22">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_approved"></a>✅ <a href="../../app/community/Proofs.lean#L877">Community.connect_approved</a> · 88 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admission_approved">Community.admission_approved</a> ↪ · 46 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_agree"></a>✅ <a href="../../app/community/Proofs.lean#L917">Community.connect_agree</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.connect_iff_trace"></a>🌐 <a href="../../app/Proofs.lean#L2884">Connection.Execution.connect_iff_trace</a> · 367 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.trace_rest"></a>🌐 <a href="../../app/Proofs.lean#L2874">Connection.Execution.trace_rest</a> · 279 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.empty_trace_store"></a>📐 <a href="../../app/Proofs.lean#L2814">Connection.Execution.empty_trace_store</a> · 241 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.world_trace_moves"></a>📐 <a href="../../app/Proofs.lean#L2804">Connection.Execution.world_trace_moves</a> · 139 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.world_step_moves"></a>📐 <a href="../../app/Proofs.lean#L2768">Connection.Execution.world_step_moves</a> · 138 below</summary><ul>
<li>📐 <a href="#law-Connection.Execution.production_step_moves">Connection.Execution.production_step_moves</a> ↪ · 136 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.production_readOnly">Connection.Execution.NodeTape.production_readOnly</a> ↪ · 85 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.onClose_goes">Connection.Execution.NodeTape.onClose_goes</a> ↪ · 44 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2755">Connection.Execution.world_run_moves</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.Moves.store_waiting">Engine.Sync.Moves.store_waiting</a> ↪ · 98 below</li>
<li><details><summary><a id="law-Engine.Sync.Moves.store_reachable"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L122">Engine.Sync.Moves.store_reachable</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.turn_reachable"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L163">Engine.Sync.turn_reachable</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_turnCapped">Engine.reach_turnCapped</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.purge_reachable"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L86">Engine.Sync.purge_reachable</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_purgeCapped">Engine.reach_purgeCapped</a> ↪ · 4 below</li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L152">Engine.Sync.held_empty_reachable</a></li>
<li>✅ <a href="../../engine/core/TurnLaws.lean#L461">Engine.waiting_empty</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.node_rest"></a>✅ <a href="../../app/connection/Proofs.lean#L781">Connection.node_rest</a> · 131 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li><details><summary><a id="law-Engine.drain_history_budget"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L61">Engine.drain_history_budget</a> · 55 below</summary><ul>
<li><details><summary><a id="law-Engine.step_history_budget"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L20">Engine.step_history_budget</a> · 54 below</summary><ul>
<li>✅ <a href="#law-Engine.waits_history_bound">Engine.waits_history_bound</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>▫️ <a href="#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.filter_lt">Engine.filter_lt</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.view_rest"></a>✅ <a href="../../engine/core/UrgentViews.lean#L173">Engine.view_rest</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Engine.drain_final"></a>✅ <a href="../../engine/core/UrgentViews.lean#L124">Engine.drain_final</a> · 35 below</summary><ul>
<li>✅ <a href="#law-Engine.step_final">Engine.step_final</a> ↪ · 34 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.inv_drainS">Engine.inv_drainS</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Engine.final_of_settled"></a>✅ <a href="../../engine/core/UrgentViews.lean#L34">Engine.final_of_settled</a> · 19 below</summary><ul>
<li>✅ <a href="#law-Engine.urgent_valid_spec">Engine.urgent_valid_spec</a> ↪ · 17 below</li>
<li>✅ <a href="#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.view_urgent"></a>▫️ <a href="../../engine/core/UrgentViews.lean#L160">Engine.view_urgent</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.eval_urgent">Engine.eval_urgent</a> ↪ · 2 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.status_rest"></a>✅ <a href="../../engine/core/UrgentViews.lean#L180">Engine.status_rest</a> · 50 below</summary><ul>
<li>✅ <a href="#law-Engine.drain_final">Engine.drain_final</a> ↪ · 35 below</li>
<li>✅ <a href="#law-Engine.final_of_settled">Engine.final_of_settled</a> ↪ · 19 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/TurnLaws.lean#L158">Engine.UrgentWaiting.settled</a></li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.connect_iff_node">Connection.connect_iff_node</a> ↪ · 115 below</li>
<li><details><summary><a id="law-Connection.reads_allowPeer_urgent"></a>✅ <a href="../../app/connection/Proofs.lean#L764">Connection.reads_allowPeer_urgent</a> · 49 below</summary><ul>
<li><details><summary><a id="law-Connection.urgentKey_member"></a>▫️ <a href="../../app/connection/Proofs.lean#L750">Connection.urgentKey_member</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Connection.urgentKey_rel"></a>✅ <a href="../../app/connection/Proofs.lean#L704">Connection.urgentKey_rel</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Engine.Rel.key_names"></a>✅ <a href="../../engine/core/Project.lean#L311">Engine.Rel.key_names</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.encode_inj">Engine.Codec.encode_inj</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Rel.key_ne_opKey"></a>✅ <a href="../../engine/core/Decl.lean#L108">Engine.Rel.key_ne_opKey</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Decl.lean#L103">Engine.encNat_small</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1601">Community.rels_short</a></li>
<li>✅ <a href="../../app/connection/Family.lean#L665">Connection.rels_apart</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rel_names_eq"></a>▫️ <a href="../../app/connection/Proofs.lean#L743">Connection.rel_names_eq</a> · 2 below</summary><ul>
<li>✅ <a href="../../app/community/Family.lean#L1599">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L732">Connection.nodup_map_inj</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.reads_allowPeer_of"></a>▫️ <a href="../../app/connection/Family.lean#L600">Community.reads_allowPeer_of</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Community.reads_live_of"></a>▫️ <a href="../../app/connection/Family.lean#L585">Community.reads_live_of</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.reads_deviceLive_of"></a>▫️ <a href="../../app/connection/Family.lean#L577">Community.reads_deviceLive_of</a> · 3 below</summary><ul>
<li>▫️ <a href="../../app/connection/Family.lean#L558">Community.reads_unremoved_of</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L755">Connection.admission_only</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L759">Connection.removal_only</a></li>
<li>▫️ <a href="../../engine/core/UrgentViews.lean#L186">Engine.View.Reads.liftL</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L774">Connection.community_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.refuse_nonmember_trace"></a>🌐 <a href="../../app/Proofs.lean#L2906">Connection.Execution.refuse_nonmember_trace</a> · 369 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.trace_rest">Connection.Execution.trace_rest</a> ↪ · 279 below</li>
<li><details><summary><a id="law-Connection.refuse_nonmember_node"></a>✅ <a href="../../app/connection/Proofs.lean#L472">Connection.refuse_nonmember_node</a> · 117 below</summary><ul>
<li><details><summary><a id="law-Connection.community_inv"></a>✅ <a href="../../app/connection/Family.lean#L686">Connection.community_inv</a> · 81 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.view_node"></a>✅ <a href="../../app/connection/Family.lean#L690">Connection.view_node</a> · 81 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
<li>✅ <a href="#law-Community.refuse_nonmember">Community.refuse_nonmember</a> ↪ · 70 below</li>
<li><details><summary><a id="law-Community.reads_allowPeer"></a>✅ <a href="../../app/connection/Family.lean#L644">Community.reads_allowPeer</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Community.reads_live"></a>✅ <a href="../../app/connection/Family.lean#L630">Community.reads_live</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.reads_deviceLive"></a>✅ <a href="../../app/connection/Family.lean#L623">Community.reads_deviceLive</a> · 3 below</summary><ul>
<li>✅ <a href="../../app/connection/Family.lean#L605">Community.reads_unremoved</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Connection.reads_allowPeer_urgent">Connection.reads_allowPeer_urgent</a> ↪ · 49 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L774">Connection.community_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.removal_cuts_off"></a>✅ <a href="../../app/community/Proofs.lean#L935">Community.removal_cuts_off</a> · 71 below</summary><ul>
<li>✅ <a href="#law-Community.refuse_nonmember">Community.refuse_nonmember</a> ↪ · 70 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.cut_stays"></a>✅ <a href="../../app/community/member/remove/Proofs.lean#L31">Community.cut_stays</a> · 9 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L22">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.cut_consented"></a>✅ <a href="../../app/community/member/Proofs.lean#L127">Community.cut_consented</a> · 48 below</summary><ul>
<li>✅ <a href="#law-Community.endpoint_signed">Community.endpoint_signed</a> ↪ · 47 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.removals_iff"></a>✅ <a href="../../app/community/Proofs.lean#L642">Community.removals_iff</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li><details><summary><a id="law-Engine.total_pos"></a>▫️ <a href="../../engine/core/Decl.lean#L188">Engine.total_pos</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/member/remove/Proofs.lean#L17">Community.byUser_args</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removal_authorized">Community.removal_authorized</a> ↪ · 47 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Connection.Execution.removal_cuts_off_trace"></a>🌐 <a href="../../app/Proofs.lean#L2894">Connection.Execution.removal_cuts_off_trace</a> · 370 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.trace_rest">Connection.Execution.trace_rest</a> ↪ · 279 below</li>
<li><details><summary><a id="law-Connection.removal_cuts_off_node"></a>✅ <a href="../../app/connection/Proofs.lean#L643">Connection.removal_cuts_off_node</a> · 118 below</summary><ul>
<li>✅ <a href="#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>✅ <a href="#law-Community.removal_cuts_off">Community.removal_cuts_off</a> ↪ · 71 below</li>
<li>✅ <a href="#law-Community.reads_allowPeer">Community.reads_allowPeer</a> ↪ · 5 below</li>
</ul></details></li>
<li>✅ <a href="#law-Connection.reads_allowPeer_urgent">Connection.reads_allowPeer_urgent</a> ↪ · 49 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L774">Connection.community_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.removed_trace"></a>🌐 <a href="../../app/Proofs.lean#L2926">Connection.Execution.removed_trace</a> · 321 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.trace_rest">Connection.Execution.trace_rest</a> ↪ · 279 below</li>
<li><details><summary><a id="law-Connection.removed_node"></a>✅ <a href="../../app/Proofs.lean#L1101">Connection.removed_node</a> · 81 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L774">Connection.community_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.mine_not_removed"></a>✅ <a href="../../app/community/Proofs.lean#L1223">Community.mine_not_removed</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Community.standing_some"></a>▫️ <a href="../../app/community/Proofs.lean#L1120">Community.standing_some</a> · 68 below</summary><ul>
<li>✅ <a href="#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li><details><summary><a id="law-Community.not_admitted_of_empty"></a>▫️ <a href="../../app/community/Proofs.lean#L1081">Community.not_admitted_of_empty</a> · 56 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1651">Community.byDevice_args</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.standing_eval"></a>▫️ <a href="../../app/community/Proofs.lean#L1101">Community.standing_eval</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.deviceLive_eval"></a>▫️ <a href="../../app/community/Proofs.lean#L1071">Community.deviceLive_eval</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1708">Community.eval_list</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.pick_some"></a>▫️ <a href="../../app/community/Proofs.lean#L1150">Community.pick_some</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1711">Community.better_cases</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.rejoin_fresh"></a>✅ <a href="../../app/community/Proofs.lean#L1246">Community.rejoin_fresh</a> · 77 below</summary><ul>
<li><details><summary><a id="law-Community.standing_cut"></a>▫️ <a href="../../app/community/Proofs.lean#L1133">Community.standing_cut</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li>▫️ <a href="#law-Community.not_admitted_of_empty">Community.not_admitted_of_empty</a> ↪ · 56 below</li>
<li>▫️ <a href="#law-Community.standing_eval">Community.standing_eval</a> ↪ · 4 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L22">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.admitted_total"></a>▫️ <a href="../../app/community/Proofs.lean#L1089">Community.admitted_total</a> · 55 below</summary><ul>
<li><details><summary><a id="law-Engine.total_rel"></a>▫️ <a href="../../engine/core/Decl.lean#L231">Engine.total_rel</a> · 51 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>▫️ <a href="#law-Engine.total_pos">Engine.total_pos</a> ↪ · 4 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1651">Community.byDevice_args</a></li>
<li>✅ <a href="../../app/community/Family.lean#L1599">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1601">Community.rels_short</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.mem_rows"></a>▫️ <a href="../../app/community/Family.lean#L1702">Community.mem_rows</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_rows_rel"></a>▫️ <a href="../../engine/core/Decl.lean#L219">Engine.mem_rows_rel</a> · 51 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_rows_all">Engine.mem_rows_all</a> ↪ · 4 below</li>
</ul></details></li>
<li>✅ <a href="../../app/community/Family.lean#L1599">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1601">Community.rels_short</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.dormant_none"></a>▫️ <a href="../../app/community/member/join/joining/Proofs.lean#L10">Community.dormant_none</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.nodeKeyOr_held"></a>▫️ <a href="../../app/community/device/endpoint/Proofs.lean#L40">Community.nodeKeyOr_held</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.pick_none"></a>▫️ <a href="../../app/community/Proofs.lean#L1202">Community.pick_none</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1708">Community.eval_list</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.join_new_device"></a>✅ <a href="../../app/community/Proofs.lean#L1282">Community.join_new_device</a> · 73 below</summary><ul>
<li>▫️ <a href="#law-Community.admitted_total">Community.admitted_total</a> ↪ · 55 below</li>
<li><details><summary><a id="law-Community.body_endpoint"></a>▫️ <a href="../../app/community/device/endpoint/Proofs.lean#L45">Community.body_endpoint</a> · 42 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1708">Community.eval_list</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.removed_stays_removed"></a>✅ <a href="../../app/community/Proofs.lean#L1329">Community.removed_stays_removed</a> · 73 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L22">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rejoin_dials"></a>✅ <a href="../../app/Proofs.lean#L1005">Connection.rejoin_dials</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Connection.dialAll_mem"></a>▫️ <a href="../../app/Proofs.lean#L985">Connection.dialAll_mem</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.dialOne_state"></a>✅ <a href="../../app/Proofs.lean#L928">Connection.dialOne_state</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Connection.requestOf_state"></a>✅ <a href="../../app/connection/Proofs.lean#L438">Connection.requestOf_state</a> · 29 below</summary><ul>
<li><details><summary><a id="law-Connection.helloOf_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L433">Connection.helloOf_state</a> · 28 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.run_view"></a>▫️ <a href="../../app/connection/Proofs.lean#L206">Connection.run_view</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/View.lean#L55">Engine.View.run_model</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L198">Connection.run_rows</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dialOne_sends"></a>✅ <a href="../../app/Proofs.lean#L917">Connection.dialOne_sends</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.dialOne_sends_mem"></a>✅ <a href="../../app/Proofs.lean#L847">Connection.dialOne_sends_mem</a> · 34 below</summary><ul>
<li>✅ <a href="#law-Connection.requestOf_state">Connection.requestOf_state</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L198">Connection.run_rows</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.reconnect_dials"></a>✅ <a href="../../app/Proofs.lean#L1027">Connection.reconnect_dials</a> · 38 below</summary><ul>
<li>▫️ <a href="#law-Connection.dialAll_mem">Connection.dialAll_mem</a> ↪ · 35 below</li>
<li>✅ <a href="#law-Connection.dialOne_sends">Connection.dialOne_sends</a> ↪ · 35 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.entry_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L978">Engine.Sync.entry_fresh</a> · 96 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onTick_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L892">Engine.Sync.onTick_fresh</a> · 87 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onTickReserved_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L854">Engine.Sync.onTickReserved_fresh</a> · 84 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L698">Engine.Sync.finish_ok</a> · 51 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sealRetries_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L607">Engine.Sync.sealRetries_ok</a> · 33 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.seal_ok">Engine.Sync.seal_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Engine.Sync.SealedOk.mono">Engine.Sync.SealedOk.mono</a> ↪ · 28 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_ok">Engine.Sync.seal_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.follow_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L502">Engine.Sync.follow_ok</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.open_ok">Engine.Sync.open_ok</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L194">Engine.Sync.ActsOk.noConn</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.endSession_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L660">Engine.Sync.endSession_goes</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Goes.bind-">Engine.Sync.Goes.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goes">Engine.Sync.Reads.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.effectsPurge_goes">Engine.Sync.effectsPurge_goes</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.flush_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L643">Engine.Sync.flush_ok</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.effectsPurge_goes">Engine.Sync.effectsPurge_goes</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.ActsOk.left"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L187">Engine.Sync.ActsOk.left</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ActsOk.right"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L181">Engine.Sync.ActsOk.right</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.apply_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L443">Engine.Sync.apply_ok</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.store_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L409">Engine.Sync.store_ok</a> · 30 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.fanout_ok">Engine.Sync.fanout_ok</a> ↪ · 28 below</li>
<li>▫️ <a href="#law-Engine.Sync.put_goes">Engine.Sync.put_goes</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.recordGiven_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L238">Engine.Sync.recordGiven_goes</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.put_goes">Engine.Sync.put_goes</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.Goes.bind-">Engine.Sync.Goes.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L61">Engine.Sync.Goes.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L194">Engine.Sync.ActsOk.noConn</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L214">Engine.Sync.ActsOk.split</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 30 below</li>
<li><details><summary><a id="law-Engine.Sync.sweepAll_ok"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L822">Engine.Sync.sweepAll_ok</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sweep_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L332">Engine.Sync.sweep_ok</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.sweep_reads">Engine.Sync.sweep_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L159">Engine.Sync.ReadOnly.afterActs</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L467">Engine.Sync.serveOwed_ok</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serveOwed_reads-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L289">Engine.Sync.serveOwed_reads'</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tickGive_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L281">Engine.Sync.tickGive_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L229">Engine.Sync.give_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.closureOps_reads">Engine.Sync.closureOps_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L277">Engine.Sync.tick_reads</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L159">Engine.Sync.ReadOnly.afterActs</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onTickDirect_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L779">Engine.Sync.onTickDirect_fresh</a> · 83 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.apply_ok">Engine.Sync.apply_ok</a> ↪ · 33 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 30 below</li>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_ok">Engine.Sync.serveOwed_ok</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.sweep_ok">Engine.Sync.sweep_ok</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.tickGive_reads">Engine.Sync.tickGive_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L159">Engine.Sync.ReadOnly.afterActs</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.FramesBy.pre"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L677">Engine.Sync.FramesBy.pre</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onFrame_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L941">Engine.Sync.onFrame_fresh</a> · 83 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onSealed_fresh"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L906">Engine.Sync.onSealed_fresh</a> · 82 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.apply_ok">Engine.Sync.apply_ok</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Engine.Sync.FramesOk.empty"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L754">Engine.Sync.FramesOk.empty</a> · 28 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.recv_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L285">Engine.Sync.recv_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onHold_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L203">Engine.Sync.onHold_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.holdsIn_reads">Engine.Sync.holdsIn_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_ok">Engine.Sync.serveOwed_ok</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 30 below</li>
<li>▫️ <a href="#law-Engine.Sync.FramesOk.empty">Engine.Sync.FramesOk.empty</a> ↪ · 28 below</li>
<li><details><summary><a id="law-Engine.Sync.write_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L232">Engine.Sync.write_goes</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Goes.forIn-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L67">Engine.Sync.Goes.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L61">Engine.Sync.Goes.pure'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Goes.getOp-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L79">Engine.Sync.Goes.getOp'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.goes">Engine.Sync.Reads.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Goes.bind-">Engine.Sync.Goes.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.Goes.turn-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L83">Engine.Sync.Goes.turn'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L61">Engine.Sync.Goes.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onWrite_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L760">Engine.Sync.onWrite_fresh</a> · 71 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 30 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onClose_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L771">Engine.Sync.onClose_fresh</a> · 52 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L194">Engine.Sync.ActsOk.noConn</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_cut_node"></a>✅ <a href="../../app/Proofs.lean#L1152">Connection.rooms_cut_node</a> · 127 below</summary><ul>
<li>✅ <a href="#law-Connection.removal_cuts_off_node">Connection.removal_cuts_off_node</a> ↪ · 118 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.connect_iff_node">Connection.connect_iff_node</a> ↪ · 115 below</li>
<li>✅ <a href="#law-Connection.rooms_cut">Connection.rooms_cut</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_trusted"></a>✅ <a href="../../app/Proofs.lean#L1110">Connection.rooms_trusted</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.mem_roomsV"></a>✅ <a href="../../app/Proofs.lean#L153">Connection.mem_roomsV</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.eval_roomsOf"></a>▫️ <a href="../../app/Proofs.lean#L144">Connection.eval_roomsOf</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.eval_roomFor"></a>✅ <a href="../../app/Proofs.lean#L128">Connection.eval_roomFor</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_cut"></a>✅ <a href="../../app/Proofs.lean#L1132">Connection.rooms_cut</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Connection.rooms_trusted">Connection.rooms_trusted</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Connection.trusts_live">Connection.trusts_live</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_removed"></a>✅ <a href="../../app/Proofs.lean#L170">Connection.rooms_removed</a> · 6 below</summary><ul>
<li>✅ <a href="#law-Connection.mem_roomsV">Connection.mem_roomsV</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Connection.eval_roomFor">Connection.eval_roomFor</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Connection.trusts_live">Connection.trusts_live</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_complete"></a>✅ <a href="../../app/Proofs.lean#L194">Connection.rooms_complete</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.eval_roomFor">Connection.eval_roomFor</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.eval_roomsOf">Connection.eval_roomsOf</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.notice_then_cut"></a>✅ <a href="../../app/Proofs.lean#L359">Connection.notice_then_cut</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Connection.roomsV_nil"></a>✅ <a href="../../app/Proofs.lean#L254">Connection.roomsV_nil</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Connection.mem_roomsV">Connection.mem_roomsV</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Connection.eval_roomFor">Connection.eval_roomFor</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Connection.trusts_live">Connection.trusts_live</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L209">Connection.has_of_mem</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.openSessions_state">Connection.openSessions_state</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Connection.allSessions_established"></a>▫️ <a href="../../app/Proofs.lean#L346">Connection.allSessions_established</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Connection.mem_sessionsOf"></a>▫️ <a href="../../app/Proofs.lean#L324">Connection.mem_sessionsOf</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L307">Connection.sessionOf_some</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L233">Connection.sessionOf_state</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.allSessions_state">Connection.allSessions_state</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.carrying_mem">Connection.carrying_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.trusts_live"></a>✅ <a href="../../app/Proofs.lean#L113">Connection.trusts_live</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L224">Connection.eval_liftL_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_model"></a>✅ <a href="../../app/Proofs.lean#L1166">Connection.rooms_model</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/View.lean#L55">Engine.View.run_model</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.recv_send">Engine.Sync.recv_send</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.Sync.recv_take"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L152">Engine.Sync.recv_take</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_send">Engine.Sync.onHold_send</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onRbsr_send">Engine.Sync.onRbsr_send</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onWant_send">Engine.Sync.onWant_send</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.start_send">Engine.Sync.start_send</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L126">Engine.Sync.recv_cases</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L32">Engine.Sync.shows_heard</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.removal_reaches_session"></a>✅ <a href="../../app/Proofs.lean#L3040">Connection.removal_reaches_session</a> · 231 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.entry_fresh">Engine.Sync.entry_fresh</a> ↪ · 96 below</li>
<li><details><summary><a id="law-Connection.hooks_readOnly"></a>✅ <a href="../../app/Proofs.lean#L2988">Connection.hooks_readOnly</a> · 84 below</summary><ul>
<li><details><summary><a id="law-Connection.hooks_reads"></a>✅ <a href="../../app/Proofs.lean#L2149">Connection.hooks_reads</a> · 83 below</summary><ul>
<li><details><summary><a id="law-Connection.react_reads"></a>▫️ <a href="../../app/Proofs.lean#L2058">Connection.react_reads</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2036">Connection.answerAll_reads</a> · 45 below</summary><ul>
<li>▫️ <a href="#law-Connection.answerOne_reads">Connection.answerOne_reads</a> ↪ · 44 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2054">Connection.establishAll_reads</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.establishReqs_reads">Connection.establishReqs_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2015">Connection.openAll_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Connection.openEach_reads">Connection.openEach_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.deliverAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2023">Connection.deliverAll_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.joinsOf_reads">Connection.joinsOf_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.endpoints_reads"></a>▫️ <a href="../../app/Proofs.lean#L1991">Connection.endpoints_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L167">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.onArrival_reads"></a>▫️ <a href="../../app/Proofs.lean#L2137">Connection.onArrival_reads</a> · 44 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.count_reads"></a>▫️ <a href="../../app/Proofs.lean#L1988">Connection.count_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L167">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.resendConns_reads"></a>▫️ <a href="../../app/Proofs.lean#L2133">Connection.resendConns_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.view_reads"></a>▫️ <a href="../../app/Proofs.lean#L1980">Connection.view_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L167">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dial_reads"></a>▫️ <a href="../../app/Proofs.lean#L2085">Connection.dial_reads</a> · 41 below</summary><ul>
<li><details><summary><a id="law-Connection.dialAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2080">Connection.dialAll_reads</a> · 39 below</summary><ul>
<li>▫️ <a href="#law-Connection.dialOne_reads">Connection.dialOne_reads</a> ↪ · 38 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.endpoints_reads">Connection.endpoints_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L167">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retired_reads"></a>▫️ <a href="../../app/Proofs.lean#L2119">Connection.retired_reads</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Connection.openSessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2111">Connection.openSessions_reads</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Connection.allSessions_reads">Connection.allSessions_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Connection.carrying_reads">Connection.carrying_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2114">Connection.sessions_reads</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Connection.openSessions_reads">Connection.openSessions_reads</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.outbox_reads"></a>▫️ <a href="../../app/Proofs.lean#L2130">Connection.outbox_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sealFor_reads"></a>▫️ <a href="../../app/Proofs.lean#L2122">Connection.sealFor_reads</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Connection.keys_reads"></a>▫️ <a href="../../app/Proofs.lean#L2000">Connection.keys_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.frameOpen_reads"></a>▫️ <a href="../../app/Proofs.lean#L2127">Connection.frameOpen_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.keys_reads">Connection.keys_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retryKey_reads"></a>▫️ <a href="../../app/Proofs.lean#L2141">Connection.retryKey_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_reads"></a>▫️ <a href="../../app/Proofs.lean#L2094">Connection.rooms_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.closing_reads"></a>▫️ <a href="../../app/Proofs.lean#L2091">Connection.closing_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sent_mayGo"></a>✅ <a href="../../app/Proofs.lean#L3002">Connection.sent_mayGo</a> · 84 below</summary><ul>
<li>✅ <a href="#law-Connection.removed_gets_only_notice">Connection.removed_gets_only_notice</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Engine.Sync.filedGive_held"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L193">Engine.Sync.filedGive_held</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filedGive_sim"></a>✅ <a href="../../engine/sync/SimLaws.lean#L157">Engine.Sync.filedGive_sim</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.notify_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L152">Engine.Sync.notify_sim</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.give_sim">Engine.Sync.give_sim</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L98">Engine.Sync.filed_sim</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.forIn-">Engine.Sync.Sim.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L56">Engine.Sync.Sim.getOp'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L32">Engine.Sync.Sim.run1</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tickGive_held"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L197">Engine.Sync.tickGive_held</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.tickGive_sim"></a>✅ <a href="../../engine/sync/SimLaws.lean#L171">Engine.Sync.tickGive_sim</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.notify_sim">Engine.Sync.notify_sim</a> ↪ · 9 below</li>
<li><details><summary><a id="law-Engine.Sync.tick_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L165">Engine.Sync.tick_sim</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.work_sim">Engine.Sync.work_sim</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L32">Engine.Sync.Sim.run1</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_shown">Engine.Sync.serveOwed_shown</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.Sync.recv_held"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L188">Engine.Sync.recv_held</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_sim"></a>✅ <a href="../../engine/sync/SimLaws.lean#L177">Engine.Sync.recv_sim</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onHold_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L94">Engine.Sync.onHold_sim</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.holdsIn_sim">Engine.Sync.holdsIn_sim</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.Sim.forIn-">Engine.Sync.Sim.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L32">Engine.Sync.Sim.run1</a></li>
</ul></details></li>
<li>✅ <a href="#law-Connection.rooms_removed">Connection.rooms_removed</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.Sync.sweep_shown"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L308">Engine.Sync.sweep_shown</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sweep_step_shown"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L299">Engine.Sync.sweep_step_shown</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Sweep.next_sent"></a>✅ <a href="../../engine/sync/SweepLaws.lean#L22">Engine.Sync.Sweep.next_sent</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/SweepLaws.lean#L5">Engine.Sync.Sweep.offer_sent</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L304">Engine.Sync.result_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_held"></a>✅ <a href="../../app/Proofs.lean#L1973">Connection.rooms_held</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Proofs.lean#L1966">Connection.view_held</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.FramesBy.mono"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L687">Engine.Sync.FramesBy.mono</a> · 28 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_sent"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L558">Engine.Sync.notice_sent</a> · 28 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_gives"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L361">Engine.Sync.give_gives</a> · 9 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.closure">Engine.Sync.closure</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.give_given"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L332">Engine.Sync.give_given</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_conn"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L317">Engine.Sync.give_conn</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureOps_state"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L77">Engine.Sync.closureOps_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.closureOps_state">Engine.Sync.closureOps_state</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.has_cons_self"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L64">Engine.Sync.has_cons_self</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filedGive_run"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L468">Engine.Sync.filedGive_run</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.notify_state"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L465">Engine.Sync.notify_state</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_state"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L305">Engine.Sync.give_state</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.closureOps_state">Engine.Sync.closureOps_state</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_given"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L512">Engine.Sync.filed_given</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Model.forIn_reads"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L505">Engine.Sync.Model.forIn_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L252">Engine.Sync.foldl_inv</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L14">Engine.run_getOp</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tickGive_run"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L475">Engine.Sync.tickGive_run</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.notify_state">Engine.Sync.notify_state</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_drop_given"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L497">Engine.Sync.tick_drop_given</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.tick_drop"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L484">Engine.Sync.tick_drop</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Conn.lean#L620">Engine.Sync.Conn.ask_drop</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L602">Engine.Sync.Conn.start_drop</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L489">Engine.Sync.Step.pulse_drop</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_given"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L542">Engine.Sync.tick_given</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Conn.lean#L630">Engine.Sync.Conn.ask_given</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L612">Engine.Sync.Conn.start_given</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L485">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.give_conn">Engine.Sync.give_conn</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closure"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L284">Engine.Sync.closure</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureOps_complete"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L137">Engine.Sync.closureOps_complete</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closureOps_sound"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L100">Engine.Sync.closureOps_sound</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_send"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L589">Engine.Sync.notice_send</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_send"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L340">Engine.Sync.give_send</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.closure">Engine.Sync.closure</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.has_of_cons"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L70">Engine.Sync.has_of_cons</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.has_cons_of"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L67">Engine.Sync.has_cons_of</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.closureOps_state">Engine.Sync.closureOps_state</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.tick_send">Engine.Sync.tick_send</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.filedGive_run">Engine.Sync.filedGive_run</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.tickGive_run">Engine.Sync.tickGive_run</a> ↪ · 4 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.filed_send">Engine.Sync.filed_send</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.give_conn">Engine.Sync.give_conn</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.removed_gets_only_notice"></a>✅ <a href="../../app/Proofs.lean#L211">Connection.removed_gets_only_notice</a> · 43 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.notice_send">Engine.Sync.notice_send</a> ↪ · 24 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.recv_send">Engine.Sync.recv_send</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Engine.Sync.recv_take">Engine.Sync.recv_take</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Connection.rooms_removed">Connection.rooms_removed</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L427">Engine.Sync.mem_notices</a></li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_once"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L620">Engine.Sync.notice_once</a> · 17 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.tick_send">Engine.Sync.tick_send</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.filedGive_run">Engine.Sync.filedGive_run</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.tickGive_run">Engine.Sync.tickGive_run</a> ↪ · 4 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.filed_send">Engine.Sync.filed_send</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/sync/NoticeLaws.lean#L408">Engine.Sync.give_quiet</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_no_holds"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L442">Engine.Sync.notice_no_holds</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.answer_trusted"></a>✅ <a href="../../app/Proofs.lean#L748">Connection.answer_trusted</a> · 69 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_trusted"></a>▫️ <a href="../../app/Proofs.lean#L676">Connection.answerAll_trusted</a> · 46 below</summary><ul>
<li><details><summary><a id="law-Connection.answerOne_out"></a>▫️ <a href="../../app/Proofs.lean#L488">Connection.answerOne_out</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L306">Connection.run_arrivedFrom</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L14">Engine.run_getOp</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.answerOne_state"></a>▫️ <a href="../../app/Proofs.lean#L640">Connection.answerOne_state</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L306">Connection.run_arrivedFrom</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L14">Engine.run_getOp</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.body_conn"></a>▫️ <a href="../../app/connection/Family.lean#L544">Connection.body_conn</a> · 37 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/connection/Proofs.lean#L26">Connection.reply_reqs</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.joinOf_not_conn"></a>▫️ <a href="../../app/Proofs.lean#L731">Connection.joinOf_not_conn</a> · 44 below</summary><ul>
<li><details><summary><a id="law-Connection.joinOf_request"></a>▫️ <a href="../../app/Proofs.lean#L595">Connection.joinOf_request</a> · 40 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishAll_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L402">Connection.establishAll_body</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Connection.establishReqs_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L385">Connection.establishReqs_body</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Connection.establishConns_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L371">Connection.establishConns_body</a> · 38 below</summary><ul>
<li>▫️ <a href="#law-Connection.body_conn">Connection.body_conn</a> ↪ · 37 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L362">Connection.openAll_body</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Connection.openEach_body"></a>▫️ <a href="../../app/connection/opened/Proofs.lean#L28">Connection.openEach_body</a> · 38 below</summary><ul>
<li>▫️ <a href="#law-Connection.body_conn">Connection.body_conn</a> ↪ · 37 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.deliverAll_join"></a>▫️ <a href="../../app/Proofs.lean#L577">Connection.deliverAll_join</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.joinsOf_join"></a>▫️ <a href="../../app/Proofs.lean#L552">Connection.joinsOf_join</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.Op.make_eta"></a>▫️ <a href="../../engine/core/Core.lean#L62">Engine.Op.make_eta</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.deliverAll_state"></a>▫️ <a href="../../app/Proofs.lean#L718">Connection.deliverAll_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L706">Connection.joinsOf_state</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L356">Connection.openAll_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L349">Connection.openEach_state</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.resend_trusted"></a>✅ <a href="../../app/Proofs.lean#L794">Connection.resend_trusted</a> · 52 below</summary><ul>
<li><details><summary><a id="law-Connection.receiptFor_receipts"></a>▫️ <a href="../../app/connection/Proofs.lean#L414">Connection.receiptFor_receipts</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L224">Connection.eval_liftL_bind</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.receipt_not_send"></a>▫️ <a href="../../app/connection/send/Proofs.lean#L10">Connection.receipt_not_send</a> · 40 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.Codec.decode_some"></a>▫️ <a href="../../engine/core/Codec.lean#L844">Engine.Codec.decode_some</a> · 3 below</summary><ul>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L831">Engine.Codec.encode_eq_enc</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.body_conn">Connection.body_conn</a> ↪ · 37 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.bare_takes_only_join"></a>✅ <a href="../../app/Proofs.lean#L611">Connection.bare_takes_only_join</a> · 62 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_conn"></a>▫️ <a href="../../app/Proofs.lean#L533">Connection.answerAll_conn</a> · 43 below</summary><ul>
<li>▫️ <a href="#law-Connection.answerOne_out">Connection.answerOne_out</a> ↪ · 41 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/connection/Proofs.lean#L10">Connection.reply_conn</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.joinOf_request">Connection.joinOf_request</a> ↪ · 40 below</li>
<li>▫️ <a href="#law-Connection.deliverAll_join">Connection.deliverAll_join</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.establishAll_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L337">Connection.establishAll_conn</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.establishReqs_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L321">Connection.establishReqs_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L308">Connection.establishConns_conn</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L297">Connection.openAll_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L284">Connection.openEach_conn</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/connection/Proofs.lean#L276">Connection.room_connOp</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><a id="law-Engine.intake_local"></a>✅ <a href="../../engine/core/Sync.lean#L59">Engine.intake_local</a></li>
<li><details><summary><a id="law-Engine.stored_local"></a>✅ <a href="../../engine/core/Sync.lean#L167">Engine.stored_local</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.stepS_ops-"></a>▫️ <a href="../../engine/core/Sync.lean#L163">Engine.stepS_ops'</a> · 7 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.foldl_ingest_ops"></a>▫️ <a href="../../engine/core/Sync.lean#L152">Engine.foldl_ingest_ops</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Sync.lean#L142">Engine.ingestS_ops</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L59">Engine.intake_local</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.local_fact_mine"></a>🪜 <a href="../../app/community/Family.lean#L1453">Community.local_fact_mine</a> · 59 below · a step of Community.order_local</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>✅ <a href="#law-Engine.stored_local">Engine.stored_local</a> ↪ · 13 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1434">Community.check_local</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.order_local"></a>✅ <a href="../../app/community/channel/message/Proofs.lean#L162">Community.order_local</a> · 65 below</summary><ul>
<li>🪜 <a href="#law-Community.local_fact_mine">Community.local_fact_mine</a> ↪ · 59 below · a step of Community.order_local</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.message_authorized">Community.message_authorized</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><a id="law-Engine.intakeConn_conn"></a>✅ <a href="../../engine/core/Sync.lean#L53">Engine.intakeConn_conn</a></li>
<li><details><summary><a id="law-Connection.established_agrees_sodium"></a>✅ <a href="../../app/Proofs.lean#L99">Connection.established_agrees_sodium</a> · 35 below</summary><ul>
<li>✅ <a href="#law-Connection.established_agrees">Connection.established_agrees</a> ↪ · 30 below</li>
<li>✅ <a href="#law-Connection.Noise.suite_good">Connection.Noise.suite_good</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.established_agrees"></a>✅ <a href="../../app/Proofs.lean#L44">Connection.established_agrees</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/wire/Noise.lean#L326">Connection.Noise.read2_write2'</a></li>
<li>✅ <a href="../../engine/wire/Noise.lean#L295">Connection.Noise.sent1_read1</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sealFor_opens"></a>✅ <a href="../../app/connection/Proofs.lean#L594">Connection.sealFor_opens</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Connection.open_seal_sodium">Connection.open_seal_sodium</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/core/Crypto.lean#L36">Engine.Bytes.of?_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.open_seal_sodium"></a>✅ <a href="../../app/connection/Proofs.lean#L574">Connection.open_seal_sodium</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.open_seal">Connection.open_seal</a> ↪ · 1 below</li>
<li>✅ <a href="../../app/connection/Proofs.lean#L564">Connection.ad_fits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.cid_seal_sodium"></a>✅ <a href="../../app/connection/Proofs.lean#L582">Connection.cid_seal_sodium</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.cid_seal">Connection.cid_seal</a> ↪ · 1 below</li>
<li>✅ <a href="../../app/connection/Proofs.lean#L564">Connection.ad_fits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.open_seal"></a>✅ <a href="../../app/connection/Proofs.lean#L518">Connection.open_seal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L511">Connection.seal_parts</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.cid_seal"></a>✅ <a href="../../app/connection/Proofs.lean#L547">Connection.cid_seal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L511">Connection.seal_parts</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.suite_good"></a>✅ <a href="../../engine/wire/Noise.lean#L430">Connection.Noise.suite_good</a> · 3 below</summary><ul>
<li>✅ <a href="../../engine/wire/Noise.lean#L421">Connection.Noise.hkdf_size</a></li>
<li>✅ <a href="../../engine/wire/Noise.lean#L415">Connection.Noise.suite_dh_comm</a></li>
<li>✅ <a href="../../engine/wire/Noise.lean#L409">Connection.Noise.suite_pub_size</a></li>
</ul></details></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Connection.Execution.production_step_moves"></a>📐 <a href="../../app/Proofs.lean#L2729">Connection.Execution.production_step_moves</a> · 136 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.production_readOnly">Connection.Execution.NodeTape.production_readOnly</a> ↪ · 85 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.step_goes"></a>▫️ <a href="../../app/Proofs.lean#L2718">Connection.Execution.NodeTape.step_goes</a> · 81 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onTick_goes"></a>▫️ <a href="../../app/Proofs.lean#L2704">Connection.Execution.NodeTape.onTick_goes</a> · 73 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.finish_goes"></a>▫️ <a href="../../app/Proofs.lean#L2652">Connection.Execution.NodeTape.finish_goes</a> · 43 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sealRetries_goes"></a>▫️ <a href="../../app/Proofs.lean#L2647">Connection.Execution.NodeTape.sealRetries_goes</a> · 35 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.seal_goes">Connection.Execution.NodeTape.seal_goes</a> ↪ · 34 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.seal_goes">Connection.Execution.NodeTape.seal_goes</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.endSession_goes"></a>▫️ <a href="../../app/Proofs.lean#L2650">Connection.Execution.NodeTape.endSession_goes</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.effectsPurge_goes">Connection.Execution.NodeTape.effectsPurge_goes</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.flush_goes"></a>▫️ <a href="../../app/Proofs.lean#L2643">Connection.Execution.NodeTape.flush_goes</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.effectsPurge_goes">Connection.Execution.NodeTape.effectsPurge_goes</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.follow_goes"></a>▫️ <a href="../../app/Proofs.lean#L2638">Connection.Execution.NodeTape.follow_goes</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.open_goes">Connection.Execution.NodeTape.open_goes</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.apply_goes"></a>▫️ <a href="../../app/Proofs.lean#L2658">Connection.Execution.NodeTape.apply_goes</a> · 26 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.store_goes"></a>▫️ <a href="../../app/Proofs.lean#L2631">Connection.Execution.NodeTape.store_goes</a> · 25 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.fanout_goes">Connection.Execution.NodeTape.fanout_goes</a> ↪ · 24 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.put_goes">Connection.Execution.NodeTape.put_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.recordGiven_goes"></a>▫️ <a href="../../app/Proofs.lean#L2621">Connection.Execution.NodeTape.recordGiven_goes</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.put_goes">Connection.Execution.NodeTape.put_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.store_goes">Connection.Execution.NodeTape.store_goes</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.serve_afterActs_goes"></a>▫️ <a href="../../app/Proofs.lean#L2689">Connection.Execution.NodeTape.serve_afterActs_goes</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.serve_goes"></a>▫️ <a href="../../app/Proofs.lean#L2662">Connection.Execution.NodeTape.serve_goes</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.serveOwed_reads">Connection.Execution.NodeTape.serveOwed_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2547">Connection.Execution.NodeTape.ReadOnly.afterActs</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sweep_afterActs_goes"></a>▫️ <a href="../../app/Proofs.lean#L2685">Connection.Execution.NodeTape.sweep_afterActs_goes</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sweep_goes"></a>▫️ <a href="../../app/Proofs.lean#L2666">Connection.Execution.NodeTape.sweep_goes</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.sweep_reads">Connection.Execution.NodeTape.sweep_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2547">Connection.Execution.NodeTape.ReadOnly.afterActs</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.sweep_goes">Connection.Execution.NodeTape.sweep_goes</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.tickGive_reads"></a>▫️ <a href="../../app/Proofs.lean#L2603">Connection.Execution.NodeTape.tickGive_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.give_reads"></a>▫️ <a href="../../app/Proofs.lean#L2593">Connection.Execution.NodeTape.give_reads</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.closure_reads">Connection.Execution.NodeTape.closure_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.turn-"></a>▫️ <a href="../../app/Proofs.lean#L2498">Connection.Execution.GoesM.turn'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onFrame_goes"></a>▫️ <a href="../../app/Proofs.lean#L2699">Connection.Execution.NodeTape.onFrame_goes</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onSealed_goes"></a>▫️ <a href="../../app/Proofs.lean#L2693">Connection.Execution.NodeTape.onSealed_goes</a> · 70 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.apply_goes">Connection.Execution.NodeTape.apply_goes</a> ↪ · 26 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.serve_goes">Connection.Execution.NodeTape.serve_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.recv_reads"></a>▫️ <a href="../../app/Proofs.lean#L2607">Connection.Execution.NodeTape.recv_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.onHold_reads">Connection.Execution.NodeTape.onHold_reads</a> ↪ · 5 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.store_goes">Connection.Execution.NodeTape.store_goes</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.write_goes"></a>▫️ <a href="../../app/Proofs.lean#L2617">Connection.Execution.NodeTape.write_goes</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.getOp-"></a>▫️ <a href="../../app/Proofs.lean#L2494">Connection.Execution.GoesM.getOp'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.turn-">Connection.Execution.GoesM.turn'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onWrite_goes"></a>▫️ <a href="../../app/Proofs.lean#L2713">Connection.Execution.NodeTape.onWrite_goes</a> · 63 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.store_goes">Connection.Execution.NodeTape.store_goes</a> ↪ · 25 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.onClose_goes">Connection.Execution.NodeTape.onClose_goes</a> ↪ · 44 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.production_readOnly"></a>▫️ <a href="../../app/Proofs.lean#L2536">Connection.Execution.NodeTape.production_readOnly</a> · 85 below</summary><ul>
<li>✅ <a href="#law-Connection.hooks_reads">Connection.hooks_reads</a> ↪ · 83 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2186">Connection.Execution.fresh_reads</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onClose_goes"></a>▫️ <a href="../../app/Proofs.lean#L2656">Connection.Execution.NodeTape.onClose_goes</a> · 44 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_turnCapped"></a>✅ <a href="../../engine/core/TurnLaws.lean#L139">Engine.reach_turnCapped</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.reach_judgeJob"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L120">Engine.reach_judgeJob</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.reach_judgeAhead"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L114">Engine.reach_judgeAhead</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L96">Engine.judgeAheadS_eq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_urgentClose"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L125">Engine.reach_urgentClose</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.reach_judgeAhead">Engine.reach_judgeAhead</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L131">Engine.reach_ingests</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_purgeCapped"></a>✅ <a href="../../engine/core/TurnLaws.lean#L652">Engine.reach_purgeCapped</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.reach_urgentClose">Engine.reach_urgentClose</a> ↪ · 2 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.waits_history_bound"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L11">Engine.waits_history_bound</a> · 51 below</summary><ul>
<li>▫️ <a href="#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li><details><summary><a id="law-Engine.waitsOk_reach"></a>▫️ <a href="../../engine/core/Budget.lean#L75">Engine.waitsOk_reach</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.waitsOk_stepS"></a>▫️ <a href="../../engine/core/Budget.lean#L49">Engine.waitsOk_stepS</a> · 7 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.waitsOk_waitOnS"></a>▫️ <a href="../../engine/core/Budget.lean#L28">Engine.waitsOk_waitOnS</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.ins_nodup"></a>▫️ <a href="../../engine/core/Model.lean#L57">Engine.ins_nodup</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_purgeS_waits"></a>▫️ <a href="../../engine/core/Purge.lean#L418">Engine.mem_purgeS_waits</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L79">Engine.byteArray_beq</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.nodup_length_le"></a>▫️ <a href="../../engine/core/Budget.lean#L101">Engine.nodup_length_le</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.filter_lt">Engine.filter_lt</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Op.ext-"></a>▫️ <a href="../../engine/core/Core.lean#L54">Engine.Op.ext'</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_stored"></a>▫️ <a href="../../engine/core/Proofs.lean#L587">Engine.reach_stored</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.filter_lt"></a>▫️ <a href="../../engine/core/Termination.lean#L30">Engine.filter_lt</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Termination.lean#L19">Engine.filter_le</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.step_final"></a>✅ <a href="../../engine/core/UrgentViews.lean#L72">Engine.step_final</a> · 34 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
<li><details><summary><a id="law-Engine.grows_step"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L153">Engine.grows_step</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.stepS_pop"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L125">Engine.stepS_pop</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.grows_decide"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L109">Engine.grows_decide</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.grows_waitOn"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L117">Engine.grows_waitOn</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Proofs.lean#L18">Engine.waitOnS_ops</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.decide_idx_other"></a>▫️ <a href="../../engine/core/UrgentViews.lean#L53">Engine.decide_idx_other</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/UrgentViews.lean#L44">Engine.indexAllS_other</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/UrgentViews.lean#L63">Engine.decide_not_urgent</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L30">Engine.waitOnS_idx</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.urgent_valid_spec"></a>✅ <a href="../../engine/core/Urgent.lean#L165">Engine.urgent_valid_spec</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.urgent_valid_iff"></a>✅ <a href="../../engine/core/Urgent.lean#L80">Engine.urgent_valid_iff</a> · 11 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.urgent_spec">Engine.urgent_spec</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.urgent_valid_closed"></a>✅ <a href="../../engine/core/Urgent.lean#L135">Engine.urgent_valid_closed</a> · 4 below</summary><ul>
<li>▫️ <a href="../../engine/core/Urgent.lean#L115">Engine.All2.mem_right</a></li>
<li>▫️ <a href="../../engine/core/Urgent.lean#L125">Engine.Sync.Reach.head</a></li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L192">Engine.allValid_forall2</a></li>
<li>▫️ <a href="../../engine/core/Urgent.lean#L101">Engine.judge_valid</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.specAt_valid_inv"></a>✅ <a href="../../engine/core/Project.lean#L105">Engine.specAt_valid_inv</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L192">Engine.allValid_forall2</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.eval_urgent"></a>▫️ <a href="../../engine/core/UrgentViews.lean#L138">Engine.eval_urgent</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L128">Engine.filterMap_congr'</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Codec.encode_inj"></a>▫️ <a href="../../engine/core/Codec.lean#L788">Engine.Codec.encode_inj</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.seal_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L548">Engine.Sync.seal_ok</a> · 31 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L466">Engine.Sync.mem_bundles</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.SealedOk.mono"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L542">Engine.Sync.SealedOk.mono</a> · 28 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.forIn_inv"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L245">Engine.Sync.forIn_inv</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.open_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L493">Engine.Sync.open_ok</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L203">Engine.Sync.ActsOk.sends</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Goes.bind-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L63">Engine.Sync.Goes.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L58">Engine.Sync.Reads.goes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.effectsPurge_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L635">Engine.Sync.effectsPurge_goes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.fanout_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L389">Engine.Sync.fanout_ok</a> · 28 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_goes">Engine.Sync.recordGiven_goes</a> ↪ · 13 below</li>
<li><details><summary><a id="law-Engine.Sync.filedGive_reads"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L239">Engine.Sync.filedGive_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filed_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L196">Engine.Sync.filed_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.give_reads">Engine.Sync.give_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L203">Engine.Sync.ActsOk.sends</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.put_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L235">Engine.Sync.put_goes</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.write_goes">Engine.Sync.write_goes</a> ↪ · 11 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.sweep_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L293">Engine.Sync.sweep_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closureOps_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L207">Engine.Sync.closureOps_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.holdsIn_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L200">Engine.Sync.holdsIn_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.forIn-"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L158">Engine.Sync.Reads.forIn'</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.answerOne_reads"></a>▫️ <a href="../../app/Proofs.lean#L2031">Connection.answerOne_reads</a> · 44 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.arrivedFrom_reads"></a>▫️ <a href="../../app/Proofs.lean#L1994">Connection.arrivedFrom_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishReqs_reads"></a>▫️ <a href="../../app/Proofs.lean#L2049">Connection.establishReqs_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.establishConns_reads"></a>▫️ <a href="../../app/Proofs.lean#L2045">Connection.establishConns_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rows_reads"></a>▫️ <a href="../../app/Proofs.lean#L1985">Connection.rows_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L167">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openEach_reads"></a>▫️ <a href="../../app/Proofs.lean#L2011">Connection.openEach_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.joinsOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2019">Connection.joinsOf_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dialOne_reads"></a>▫️ <a href="../../app/Proofs.lean#L2075">Connection.dialOne_reads</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Connection.requestOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2066">Connection.requestOf_reads</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Connection.helloOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2006">Connection.helloOf_reads</a> · 32 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.connectedTo_reads"></a>▫️ <a href="../../app/Proofs.lean#L2003">Connection.connectedTo_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L167">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.allSessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2104">Connection.allSessions_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionsOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2100">Connection.sessionsOf_reads</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2097">Connection.sessionOf_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.arrival_reads"></a>▫️ <a href="../../app/Proofs.lean#L1997">Connection.arrival_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.carrying_reads"></a>▫️ <a href="../../app/Proofs.lean#L2107">Connection.carrying_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.give_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L142">Engine.Sync.give_sim</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureOps_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L120">Engine.Sync.closureOps_sim</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L56">Engine.Sync.Sim.getOp'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L103">Engine.Sync.closureOps_cons</a></li>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L116">Engine.Sync.closureOps_zero</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Sim.forIn-"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L44">Engine.Sync.Sim.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Sim.bind-"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L38">Engine.Sync.Sim.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.work_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L161">Engine.Sync.work_sim</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.holdsIn_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L91">Engine.Sync.holdsIn_sim</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L56">Engine.Sync.Sim.getOp'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.seal_goes"></a>▫️ <a href="../../app/Proofs.lean#L2645">Connection.Execution.NodeTape.seal_goes</a> · 34 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.GoesM.forIn-"></a>▫️ <a href="../../app/Proofs.lean#L2482">Connection.Execution.GoesM.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.GoesM.bind-"></a>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.effectsPurge_goes"></a>▫️ <a href="../../app/Proofs.lean#L2641">Connection.Execution.NodeTape.effectsPurge_goes</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.purge-"></a>▫️ <a href="../../app/Proofs.lean#L2500">Connection.Execution.GoesM.purge'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.goesM"></a>▫️ <a href="../../app/Proofs.lean#L2474">Engine.Sync.Reads.goesM</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.open_goes"></a>▫️ <a href="../../app/Proofs.lean#L2635">Connection.Execution.NodeTape.open_goes</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.fanout_goes"></a>▫️ <a href="../../app/Proofs.lean#L2627">Connection.Execution.NodeTape.fanout_goes</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.recordGiven_goes">Connection.Execution.NodeTape.recordGiven_goes</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.filedGive_reads"></a>▫️ <a href="../../app/Proofs.lean#L2601">Connection.Execution.NodeTape.filedGive_reads</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.give_reads">Connection.Execution.NodeTape.give_reads</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.filed_reads"></a>▫️ <a href="../../app/Proofs.lean#L2570">Connection.Execution.NodeTape.filed_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2478">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.put_goes"></a>▫️ <a href="../../app/Proofs.lean#L2619">Connection.Execution.NodeTape.put_goes</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.write_goes">Connection.Execution.NodeTape.write_goes</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.serveOwed_reads"></a>▫️ <a href="../../app/Proofs.lean#L2610">Connection.Execution.NodeTape.serveOwed_reads</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.read_program"></a>▫️ <a href="../../app/Proofs.lean#L2558">Connection.Execution.NodeTape.read_program</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.refresh_reads"></a>▫️ <a href="../../app/Proofs.lean#L2625">Connection.Execution.NodeTape.refresh_reads</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sweep_reads"></a>▫️ <a href="../../app/Proofs.lean#L2552">Connection.Execution.NodeTape.sweep_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.closure_reads"></a>▫️ <a href="../../app/Proofs.lean#L2572">Connection.Execution.NodeTape.closure_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L103">Engine.Sync.closureOps_cons</a></li>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L116">Engine.Sync.closureOps_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onHold_reads"></a>▫️ <a href="../../app/Proofs.lean#L2567">Connection.Execution.NodeTape.onHold_reads</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.holdsIn_reads"></a>▫️ <a href="../../app/Proofs.lean#L2565">Connection.Execution.NodeTape.holdsIn_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L155">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
</ul>
