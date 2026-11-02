# Quality proofs › The screen

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › The screen**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1348) · 🌐 world: the node's code in a World (69) · 🪜 step: a step of a wired law (59) · 📐 model: over a model (73) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2124)

<ul>
<li><a id="law-Demand.owned_iff"></a>✅ <a href="../../engine/renderer/Demand.lean#L152">Demand.owned_iff</a></li>
<li><a id="law-Demand.complete_retired"></a>✅ <a href="../../engine/renderer/Demand.lean#L103">Demand.complete_retired</a></li>
<li><a id="law-Demand.next_visible"></a>✅ <a href="../../engine/renderer/Demand.lean#L156">Demand.next_visible</a></li>
<li><a id="law-Demand.retained_prefix"></a>✅ <a href="../../engine/renderer/Demand.lean#L172">Demand.retained_prefix</a></li>
<li><details><summary><a id="law-Demand.retained_ticket"></a>✅ <a href="../../engine/renderer/Demand.lean#L215">Demand.retained_ticket</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Demand.reconcile_ticket_none"></a>✅ <a href="../../engine/renderer/Demand.lean#L199">Demand.reconcile_ticket_none</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Demand.reconcile_keys"></a>✅ <a href="../../engine/renderer/Demand.lean#L186">Demand.reconcile_keys</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Demand.assigned_key"></a>✅ <a href="../../engine/renderer/Demand.lean#L180">Demand.assigned_key</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Demand.lean#L176">Demand.ticket_key</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="../../engine/renderer/Demand.lean#L195">Demand.ticket_none</a></li>
</ul></details></li>
<li><details><summary><a id="law-Demand.reconcile_ticket_origin"></a>✅ <a href="../../engine/renderer/Demand.lean#L204">Demand.reconcile_ticket_origin</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Demand.assigned_key">Demand.assigned_key</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/renderer/Demand.lean#L176">Demand.ticket_key</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Demand.remount_rejects"></a>✅ <a href="../../engine/renderer/Demand.lean#L267">Demand.remount_rejects</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Demand.remount_fresh"></a>✅ <a href="../../engine/renderer/Demand.lean#L256">Demand.remount_fresh</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Demand.reconcile_ticket_none">Demand.reconcile_ticket_none</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Demand.fresh_ticket"></a>✅ <a href="../../engine/renderer/Demand.lean#L224">Demand.fresh_ticket</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Demand.reconcile_ticket_origin">Demand.reconcile_ticket_origin</a> ↪ · 2 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/renderer/Demand.lean#L142">Demand.serial_monotone</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/renderer/Demand.lean#L176">Demand.ticket_key</a></li>
</ul></details></li>
<li><a id="law-Work.request_again"></a>✅ <a href="../../engine/renderer/Work.lean#L159">Work.request_again</a></li>
<li><a id="law-Demand.next_map"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L8">Demand.next_map</a></li>
<li><details><summary><a id="law-Demand.takeBy_map"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L17">Demand.takeBy_map</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/DemandRank.lean#L8">Demand.next_map</a></li>
</ul></details></li>
<li><a id="law-Demand.filter_rank"></a>🪜 <a href="../../engine/renderer/DemandRank.lean#L29">Demand.filter_rank</a> · a step of Demand.selected_or_retired, Demand.selected_within, Demand.take_changes +1</li>
<li><details><summary><a id="law-Demand.take_progress"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L46">Demand.take_progress</a> · 1 below</summary><ul>
<li>🪜 <a href="../../engine/renderer/DemandRank.lean#L29">Demand.filter_rank</a> · a step of Demand.selected_or_retired, Demand.selected_within, Demand.take_changes +1</li>
</ul></details></li>
<li><details><summary><a id="law-Demand.take_changes"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L89">Demand.take_changes</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Demand.take_progress">Demand.take_progress</a> ↪ · 1 below</li>
<li>🪜 <a href="../../engine/renderer/DemandRank.lean#L29">Demand.filter_rank</a> · a step of Demand.selected_or_retired, Demand.selected_within, Demand.take_changes +1</li>
</ul></details></li>
<li><details><summary><a id="law-Demand.selected_or_retired"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L118">Demand.selected_or_retired</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Demand.take_changes">Demand.take_changes</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Demand.selected_within"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L138">Demand.selected_within</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Demand.selected_or_retired">Demand.selected_or_retired</a> ↪ · 3 below</li>
</ul></details></li>
<li><a id="law-Demand.take_first"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L176">Demand.take_first</a></li>
<li><a id="law-Demand.take_sorted"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L190">Demand.take_sorted</a></li>
<li><a id="law-Demand.reconcileFirst_sorted"></a>✅ <a href="../../engine/renderer/DemandRank.lean#L165">Demand.reconcileFirst_sorted</a></li>
<li><a id="law-Demand.shipped_late"></a>🧪 <a href="../../engine/renderer/DemandRank.lean#L207">Demand.shipped_late</a></li>
<li><a id="law-LifecycleLaws.unmount_read"></a>✅ <a href="../../app/Proofs.lean#L1186">LifecycleLaws.unmount_read</a></li>
<li><a id="law-LifecycleLaws.unmount_write"></a>✅ <a href="../../app/Proofs.lean#L1192">LifecycleLaws.unmount_write</a></li>
<li><details><summary><a id="law-LifecycleLaws.old_callback"></a>✅ <a href="../../app/Proofs.lean#L1198">LifecycleLaws.old_callback</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Screen.lean#L234">Lifecycle.old_quiet</a></li>
</ul></details></li>
<li><a id="law-Lifecycle.unmounted_quiet"></a>✅ <a href="../../app/Screen.lean#L230">Lifecycle.unmounted_quiet</a></li>
<li><a id="law-Lifecycle.old_quiet"></a>✅ <a href="../../app/Screen.lean#L234">Lifecycle.old_quiet</a></li>
<li><details><summary><a id="law-Lifecycle.live_exact"></a>✅ <a href="../../app/Screen.lean#L242">Lifecycle.live_exact</a> · 3 below</summary><ul>
<li><details><summary><a id="law-LiveLaws.q_lawful"></a>▫️ <a href="../../app/Commands.lean#L901">LiveLaws.q_lawful</a> · 2 below</summary><ul>
<li><details><summary><a id="law-LiveLaws.listQ_lawful"></a>▫️ <a href="../../app/Commands.lean#L883">LiveLaws.listQ_lawful</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Commands.lean#L877">LiveLaws.byteArray_lawful</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Commands.lean#L877">LiveLaws.byteArray_lawful</a></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Lifecycle.mounted_runs"></a>✅ <a href="../../app/Screen.lean#L294">Lifecycle.mounted_runs</a></li>
<li><details><summary><a id="law-Lifecycle.restore_checkpoint"></a>✅ <a href="../../app/Screen.lean#L290">Lifecycle.restore_checkpoint</a> · 36 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><a id="law-App.page_round"></a>✅ <a href="../../app/Screen.lean#L2057">App.page_round</a></li>
<li><details><summary><a id="law-LifecycleLaws.restore_page_anchor"></a>✅ <a href="../../app/Proofs.lean#L1210">LifecycleLaws.restore_page_anchor</a> · 42 below</summary><ul>
<li>✅ <a href="#law-Lifecycle.restore_checkpoint">Lifecycle.restore_checkpoint</a> ↪ · 36 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-LifecycleLaws.apply_page_anchor"></a>✅ <a href="../../app/Proofs.lean#L1220">LifecycleLaws.apply_page_anchor</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>✅ <a href="../../engine/renderer/Nav.lean#L89">Nav.go_page</a></li>
</ul></details></li>
<li><a id="law-Lifecycle.resize_anchor"></a>✅ <a href="../../app/Screen.lean#L258">Lifecycle.resize_anchor</a></li>
<li><details><summary><a id="law-LifecycleLaws.viewport_geometry"></a>✅ <a href="../../app/Proofs.lean#L1236">LifecycleLaws.viewport_geometry</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Geometry.pinned_tap">Geometry.pinned_tap</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Geometry.placed_row"></a>✅ <a href="../../engine/renderer/Geometry.lean#L86">Geometry.placed_row</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Geometry.lean#L77">Geometry.view_shift</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Surface.visible_in_viewport"></a>✅ <a href="../../engine/renderer/Surface.lean#L124">Surface.visible_in_viewport</a> · 6 below</summary><ul>
<li>✅ <a href="#law-Surface.placed_row">Surface.placed_row</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/renderer/Geometry.lean#L95">Geometry.visible_in_viewport</a></li>
<li>✅ <a href="../../engine/renderer/Surface.lean#L70">Surface.crop_row</a></li>
</ul></details></li>
<li><details><summary><a id="law-Geometry.newest_visible"></a>✅ <a href="../../engine/renderer/Geometry.lean#L105">Geometry.newest_visible</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Geometry.lean#L95">Geometry.visible_in_viewport</a></li>
</ul></details></li>
<li><details><summary><a id="law-Surface.pinned_visible"></a>✅ <a href="../../engine/renderer/Surface.lean#L141">Surface.pinned_visible</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Geometry.lean#L152">Geometry.pinned_visible</a></li>
<li>✅ <a href="../../engine/renderer/Surface.lean#L115">Surface.row_pinned</a></li>
</ul></details></li>
<li><details><summary><a id="law-Geometry.pinned_tap"></a>✅ <a href="../../engine/renderer/Geometry.lean#L158">Geometry.pinned_tap</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Geometry.lean#L77">Geometry.view_shift</a></li>
</ul></details></li>
<li><details><summary><a id="law-SheetGeom.hit_iff"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L125">SheetGeom.hit_iff</a> · 2 below</summary><ul>
<li><details><summary><a id="law-SheetGeom.mod_eq"></a>▫️ <a href="../../engine/renderer/SheetGeom.lean#L117">SheetGeom.mod_eq</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/SheetGeom.lean#L112">SheetGeom.div_eq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/SheetGeom.lean#L112">SheetGeom.div_eq</a></li>
</ul></details></li>
<li><a id="law-NodeOffer.offer_split"></a>✅ <a href="../../app/Screen.lean#L378">NodeOffer.offer_split</a></li>
<li><details><summary><a id="law-NodeOffer.offer_runs"></a>✅ <a href="../../app/Screen.lean#L415">NodeOffer.offer_runs</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Screen.lean#L378">NodeOffer.offer_split</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.eval_stable"></a>✅ <a href="../../engine/core/View.lean#L141">Engine.eval_stable</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Engine.later_inv"></a>▫️ <a href="../../engine/core/View.lean#L122">Engine.later_inv</a> · 28 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_ingest">Engine.inv_ingest</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.later_keeps"></a>▫️ <a href="../../engine/core/View.lean#L115">Engine.later_keeps</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.stepS_keeps"></a>▫️ <a href="../../engine/core/View.lean#L93">Engine.stepS_keeps</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L88">Engine.ingestS_status</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L128">Engine.filterMap_congr'</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.view_stable"></a>✅ <a href="../../engine/core/View.lean#L164">Engine.view_stable</a> · 34 below</summary><ul>
<li>✅ <a href="#law-Engine.eval_stable">Engine.eval_stable</a> ↪ · 33 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.filed_rel"></a>✅ <a href="../../engine/core/Decl.lean#L200">Engine.filed_rel</a> · 45 below</summary><ul>
<li>✅ <a href="#law-Engine.mem_keysOf">Engine.mem_keysOf</a> ↪ · 32 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_keysOf"></a>✅ <a href="../../engine/core/Decl.lean#L89">Engine.mem_keysOf</a> · 32 below</summary><ul>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.Rel.key_eq_iff">Engine.Rel.key_eq_iff</a> ↪ · 30 below</li>
<li>▫️ <a href="../../engine/core/Decl.lean#L74">Engine.Rel.eq_of_names</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.matching_nodup"></a>✅ <a href="../../engine/core/Decl.lean#L168">Engine.matching_nodup</a> · 3 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.perm_sortPos">Engine.perm_sortPos</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Decl.lean#L159">Engine.nodup_filterMap_ids</a></li>
</ul></details></li>
<li><details><summary><a id="law-Live.record_indexed"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L506">Live.record_indexed</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Live.push_adds"></a>▫️ <a href="../../engine/renderer/RestLaws.lean#L473">Live.push_adds</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/RestLaws.lean#L463">Live.push_keeps</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/RestLaws.lean#L482">Live.filter_keeps</a></li>
<li>▫️ <a href="../../engine/renderer/RestLaws.lean#L463">Live.push_keeps</a></li>
</ul></details></li>
<li><details><summary><a id="law-Live.marked_complete"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L525">Live.marked_complete</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Live.mem_markHit"></a>▫️ <a href="../../engine/renderer/RestLaws.lean#L97">Live.mem_markHit</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Live.mem_markHitM"></a>▫️ <a href="../../engine/renderer/RestLaws.lean#L78">Live.mem_markHitM</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/RestLaws.lean#L62">Live.mem_foldl_insert</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/ReaderLaws.lean#L66">Live.mem_filter'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Live.dirty_marked"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L534">Live.dirty_marked</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Live.mem_markHit">Live.mem_markHit</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/renderer/ReaderLaws.lean#L66">Live.mem_filter'</a></li>
</ul></details></li>
<li><a id="law-Live.record_dirty"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L540">Live.record_dirty</a></li>
<li><details><summary><a id="law-Live.fresh_record"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L581">Live.fresh_record</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/RestLaws.lean#L561">Live.put_get_other</a></li>
<li>▫️ <a href="../../engine/renderer/RestLaws.lean#L570">Live.put_get_self</a></li>
<li>✅ <a href="../../engine/renderer/RestLaws.lean#L540">Live.record_dirty</a></li>
</ul></details></li>
<li><details><summary><a id="law-Live.fresh_notice"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L605">Live.fresh_notice</a> · 6 below</summary><ul>
<li>✅ <a href="#law-Live.dirty_marked">Live.dirty_marked</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Live.marked_complete">Live.marked_complete</a> ↪ · 4 below</li>
</ul></details></li>
<li><a id="law-Live.fresh_keep"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L631">Live.fresh_keep</a></li>
<li><a id="law-Live.settle_fresh"></a>✅ <a href="../../engine/renderer/RestLaws.lean#L621">Live.settle_fresh</a></li>
<li><a id="law-Engine.readPlan_cost"></a>✅ <a href="../../engine/core/Query.lean#L563">Engine.readPlan_cost</a></li>
<li><a id="law-Engine.readPlan_cost_range"></a>✅ <a href="../../engine/core/Query.lean#L575">Engine.readPlan_cost_range</a></li>
<li><details><summary><a id="law-Engine.readPlan_cost_le"></a>✅ <a href="../../engine/core/Query.lean#L614">Engine.readPlan_cost_le</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Engine.plan_stmt_cost">Engine.plan_stmt_cost</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.plan_stmt_cost"></a>✅ <a href="../../engine/core/Query.lean#L601">Engine.plan_stmt_cost</a> · 1 below</summary><ul>
<li>🪜 <a href="../../engine/core/Query.lean#L586">Engine.Stmt.walks_le</a> · a step of Engine.plan_stmt_cost, Engine.readPlan_cost_le</li>
</ul></details></li>
<li><a id="law-Engine.splitWalk_exact"></a>✅ <a href="../../engine/core/Query.lean#L677">Engine.splitWalk_exact</a></li>
<li><a id="law-Engine.splitWalk_steps"></a>✅ <a href="../../engine/core/Query.lean#L692">Engine.splitWalk_steps</a></li>
<li><details><summary><a id="law-Engine.splitWalk_cost"></a>✅ <a href="../../engine/core/Query.lean#L739">Engine.splitWalk_cost</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Query.lean#L692">Engine.splitWalk_steps</a></li>
</ul></details></li>
<li><a id="law-Engine.sideCount_run"></a>📐 <a href="../../engine/core/Query.lean#L667">Engine.sideCount_run</a></li>
<li><details><summary><a id="law-Engine.notice_iff"></a>✅ <a href="../../engine/core/WindowLaws.lean#L705">Engine.notice_iff</a> · 145 below</summary><ul>
<li><details><summary><a id="law-Engine.window_ne_iff_flips"></a>✅ <a href="../../engine/core/WindowLaws.lean#L651">Engine.window_ne_iff_flips</a> · 117 below</summary><ul>
<li>✅ <a href="#law-Engine.run_exact">Engine.run_exact</a> ↪ · 73 below</li>
<li><details><summary><a id="law-Engine.run_inv"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L439">Engine.run_inv</a> · 56 below</summary><ul>
<li><details><summary><a id="law-Engine.change_inv"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L416">Engine.change_inv</a> · 55 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.purge_inv">Engine.purge_inv</a> ↪ · 34 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_ingest">Engine.inv_ingest</a> ↪ · 8 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.window_ne_iff"></a>✅ <a href="../../engine/core/WindowLaws.lean#L607">Engine.window_ne_iff</a> · 31 below</summary><ul>
<li><details><summary><a id="law-Engine.window_strict"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L558">Engine.window_strict</a> · 24 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.sortPos_sorted">Engine.sortPos_sorted</a> ↪ · 15 below</li>
<li><details><summary><a id="law-Engine.strict_of"></a>▫️ <a href="../../engine/core/Order.lean#L51">Engine.strict_of</a> · 10 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.matching_nodup">Engine.matching_nodup</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.eq_of_strict"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L573">Engine.eq_of_strict</a> · 13 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_window"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L546">Engine.mem_window</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.filed_iff"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L184">Engine.filed_iff</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.filed_iff">Engine.filed_iff</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.fact_stable">Engine.fact_stable</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Engine.run_extends"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L475">Engine.run_extends</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.change_extends"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L462">Engine.change_extends</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/WindowLaws.lean#L451">Engine.ingest_extends</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Subs.mem_notifyM"></a>✅ <a href="../../engine/core/WindowIndex.lean#L537">Engine.Subs.mem_notifyM</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Engine.Subs.find_iff"></a>✅ <a href="../../engine/core/WindowIndex.lean#L347">Engine.Subs.find_iff</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Engine.find_build"></a>✅ <a href="../../engine/core/WindowIndex.lean#L282">Engine.find_build</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Engine.strictB_boundsOf"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L181">Engine.strictB_boundsOf</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.dedupSorted_strict">Engine.dedupSorted_strict</a> ↪ · 21 below</li>
<li>▫️ <a href="#law-Engine.posLe_trans">Engine.posLe_trans</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.posLe_total">Engine.posLe_total</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.rank_spec"></a>✅ <a href="../../engine/core/WindowIndex.lean#L84">Engine.rank_spec</a> · 21 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L68">Engine.getD_pos</a></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L72">Engine.rankM_id</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.gapHi_eq"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L242">Engine.gapHi_eq</a> · 19 below</summary><ul>
<li>▫️ <a href="#law-Engine.StrictB.le">Engine.StrictB.le</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.StrictB.gt">Engine.StrictB.gt</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Pos.gt_swap">Engine.Pos.gt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Pos.lt_swap">Engine.Pos.lt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L68">Engine.getD_pos</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.gapLo_eq"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L217">Engine.gapLo_eq</a> · 19 below</summary><ul>
<li>▫️ <a href="#law-Engine.StrictB.le">Engine.StrictB.le</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.StrictB.gt">Engine.StrictB.gt</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Pos.gt_swap">Engine.Pos.gt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Pos.lt_swap">Engine.Pos.lt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L68">Engine.getD_pos</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Engine.end_bound"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L193">Engine.end_bound</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_boundsOf">Engine.mem_boundsOf</a> ↪ · 11 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
<li>▫️ <a href="#law-Engine.Pos.gt_swap">Engine.Pos.gt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Pos.lt_swap">Engine.Pos.lt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L68">Engine.getD_pos</a></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L269">Engine.mem_cover</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_net"></a>✅ <a href="../../engine/core/WindowIndex.lean#L585">Engine.mem_net</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.contains_foldl"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L567">Engine.contains_foldl</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.contains_toggle"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L550">Engine.contains_toggle</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.read_notice_iff"></a>✅ <a href="../../engine/core/WindowRead.lean#L417">Engine.read_notice_iff</a> · 174 below</summary><ul>
<li>✅ <a href="#law-Engine.notice_iff">Engine.notice_iff</a> ↪ · 145 below</li>
<li>✅ <a href="#law-Engine.read_rows_iff">Engine.read_rows_iff</a> ↪ · 56 below</li>
<li>▫️ <a href="#law-Engine.run_inv">Engine.run_inv</a> ↪ · 56 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.read_rows_iff"></a>✅ <a href="../../engine/core/WindowRead.lean#L288">Engine.read_rows_iff</a> · 56 below</summary><ul>
<li><details><summary><a id="law-Engine.inRange_strict"></a>▫️ <a href="../../engine/core/WindowRead.lean#L175">Engine.inRange_strict</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.window_strict">Engine.window_strict</a> ↪ · 24 below</li>
<li><details><summary><a id="law-Engine.window_range"></a>▫️ <a href="../../engine/core/WindowRead.lean#L168">Engine.window_range</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.rangeWin_inside"></a>▫️ <a href="../../engine/core/WindowRead.lean#L165">Engine.rangeWin_inside</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L153">Engine.above_after</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L159">Engine.below_before</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L150">Engine.inside_eq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L142">Engine.matching_key</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.window_cutD"></a>▫️ <a href="../../engine/core/WindowRead.lean#L210">Engine.window_cutD</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.after_of_ge"></a>▫️ <a href="../../engine/core/WindowRead.lean#L180">Engine.after_of_ge</a> · 24 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Engine.geP_iff"></a>▫️ <a href="../../engine/core/WindowRead.lean#L100">Engine.geP_iff</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_self"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L36">Engine.Pos.cmp_self</a> · 10 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Pos.gt_swap">Engine.Pos.gt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Pos.lt_swap">Engine.Pos.lt_swap</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L150">Engine.inside_eq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L159">Engine.below_before</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L150">Engine.inside_eq</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L142">Engine.matching_key</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.window_cutA"></a>▫️ <a href="../../engine/core/WindowRead.lean#L225">Engine.window_cutA</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.before_of_le"></a>▫️ <a href="../../engine/core/WindowRead.lean#L195">Engine.before_of_le</a> · 22 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Engine.leP_iff"></a>▫️ <a href="../../engine/core/WindowRead.lean#L111">Engine.leP_iff</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_self">Engine.Pos.cmp_self</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L150">Engine.inside_eq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L153">Engine.above_after</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L150">Engine.inside_eq</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L142">Engine.matching_key</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.geP_closed"></a>▫️ <a href="../../engine/core/WindowRead.lean#L119">Engine.geP_closed</a> · 22 below</summary><ul>
<li><details><summary><a id="law-Engine.aheadD_trans"></a>▫️ <a href="../../engine/core/WindowRead.lean#L90">Engine.aheadD_trans</a> · 19 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.geP_iff">Engine.geP_iff</a> ↪ · 14 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.leP_closed"></a>▫️ <a href="../../engine/core/WindowRead.lean#L125">Engine.leP_closed</a> · 22 below</summary><ul>
<li><details><summary><a id="law-Engine.aheadA_trans"></a>▫️ <a href="../../engine/core/WindowRead.lean#L92">Engine.aheadA_trans</a> · 19 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.leP_iff">Engine.leP_iff</a> ↪ · 11 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.aheadA_trans">Engine.aheadA_trans</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.aheadD_trans">Engine.aheadD_trans</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.geP_iff">Engine.geP_iff</a> ↪ · 14 below</li>
<li><details><summary><a id="law-Engine.aheadA_irr"></a>▫️ <a href="../../engine/core/WindowRead.lean#L89">Engine.aheadA_irr</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_self">Engine.Pos.cmp_self</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.aheadD_irr"></a>▫️ <a href="../../engine/core/WindowRead.lean#L88">Engine.aheadD_irr</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_self">Engine.Pos.cmp_self</a> ↪ · 10 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.leP_iff">Engine.leP_iff</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.window_range">Engine.window_range</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.cut_iff"></a>▫️ <a href="../../engine/core/WindowRead.lean#L243">Engine.cut_iff</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.cut_top"></a>▫️ <a href="../../engine/core/WindowRead.lean#L55">Engine.cut_top</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L26">Engine.mem_last_or</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L35">Engine.partition_thr</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L139">Engine.eval_rows</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L278">Engine.win_cut</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L268">Engine.win_none</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L271">Engine.win_uncut</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.window_rows"></a>✅ <a href="../../engine/core/WindowRead.lean#L360">Engine.window_rows</a> · 52 below</summary><ul>
<li>▫️ <a href="#law-Engine.inRange_strict">Engine.inRange_strict</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Engine.window_cutD">Engine.window_cutD</a> ↪ · 27 below</li>
<li>▫️ <a href="#law-Engine.window_cutA">Engine.window_cutA</a> ↪ · 25 below</li>
<li>▫️ <a href="#law-Engine.aheadA_trans">Engine.aheadA_trans</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.aheadD_trans">Engine.aheadD_trans</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.geP_iff">Engine.geP_iff</a> ↪ · 14 below</li>
<li>▫️ <a href="#law-Engine.aheadA_irr">Engine.aheadA_irr</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.aheadD_irr">Engine.aheadD_irr</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.leP_iff">Engine.leP_iff</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.window_range">Engine.window_range</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.cut_top">Engine.cut_top</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L139">Engine.eval_rows</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L278">Engine.win_cut</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L268">Engine.win_none</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L271">Engine.win_uncut</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.watch_stable"></a>✅ <a href="../../engine/core/WindowRead.lean#L451">Engine.watch_stable</a> · 59 below</summary><ul>
<li>✅ <a href="#law-Engine.read_rows_iff">Engine.read_rows_iff</a> ↪ · 56 below</li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L436">Engine.eval_eq</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L142">Engine.matching_key</a></li>
<li>▫️ <a href="../../engine/core/WindowRead.lean#L440">Engine.window_all</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.run_exact"></a>✅ <a href="../../engine/core/WindowLaws.lean#L431">Engine.run_exact</a> · 73 below</summary><ul>
<li>▫️ <a href="#law-Engine.change_inv">Engine.change_inv</a> ↪ · 55 below</li>
<li><details><summary><a id="law-Engine.change_exact"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L421">Engine.change_exact</a> · 26 below</summary><ul>
<li><details><summary><a id="law-Engine.purge_exact"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L374">Engine.purge_exact</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.countP_purgeBlock"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L335">Engine.countP_purgeBlock</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.countP_fileJ_le"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L316">Engine.countP_fileJ_le</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.countP_eq_nodup">Engine.countP_eq_nodup</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.nodup_nubB">Engine.nodup_nubB</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.flips_fileJ"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L219">Engine.flips_fileJ</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.countP_eq_nodup">Engine.countP_eq_nodup</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.nodup_nubB">Engine.nodup_nubB</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.mem_nubB">Engine.mem_nubB</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.filed_iff">Engine.filed_iff</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.mem_purgeS_idx">Engine.mem_purgeS_idx</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.nodup_nubB">Engine.nodup_nubB</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.sum_map_single"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L80">Engine.sum_map_single</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.mem_nubB">Engine.mem_nubB</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.purgeS_status_mem">Engine.purgeS_status_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.purgeS_status_not">Engine.purgeS_status_not</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/WindowLaws.lean#L211">Engine.fileJ_pos</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.step_exact"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L241">Engine.step_exact</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.flips_fileJ">Engine.flips_fileJ</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L30">Engine.waitOnS_idx</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ingest_exact"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L204">Engine.ingest_exact</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowLaws.lean#L173">Engine.flips_nil</a></li>
<li>▫️ <a href="../../engine/core/WindowLaws.lean#L201">Engine.ingestS_idx</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L88">Engine.ingestS_status</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowLaws.lean#L175">Engine.flips_append</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.fact_stable"></a>✅ <a href="../../engine/core/WindowLaws.lean#L514">Engine.fact_stable</a> · 18 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.spec_closure"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L500">Engine.spec_closure</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_inv">Engine.spec_valid_inv</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/core/WindowLaws.lean#L490">Engine.All2.mem_left</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_inv">Engine.spec_valid_inv</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.find_costs"></a>✅ <a href="../../engine/core/WindowCost.lean#L136">Engine.find_costs</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.slots_find_costs"></a>▫️ <a href="../../engine/core/WindowCost.lean#L85">Engine.slots_find_costs</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.rank_costs"></a>✅ <a href="../../engine/core/WindowCost.lean#L56">Engine.rank_costs</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.costs_bind_le"></a>▫️ <a href="../../engine/core/Cost.lean#L414">Engine.costs_bind_le</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Costs.mono"></a>🪜 <a href="../../engine/core/Cost.lean#L397">Engine.Costs.mono</a> · 3 below · a step of Engine.decide_costs, Engine.decide_reads, Engine.find_costs +9</summary><ul>
<li>▫️ <a href="#law-Engine.Field.mono">Engine.Field.mono</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Cost.lean#L191">Engine.Within.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.costs_bind"></a>🪜 <a href="../../engine/core/Cost.lean#L410">Engine.costs_bind</a> · 1 below · a step of Engine.decide_costs, Engine.decide_reads, Engine.find_costs +9</summary><ul>
<li>🪜 <a href="../../engine/core/Cost.lean#L211">Engine.within_bind</a> · a step of Engine.View.view_lists, Engine.decide_costs, Engine.decide_reads +10</li>
</ul></details></li>
</ul></details></li>
<li>🪜 <a href="#law-Engine.Costs.mono">Engine.Costs.mono</a> ↪ · 3 below · a step of Engine.decide_costs, Engine.decide_reads, Engine.find_costs +9</li>
<li><details><summary><a id="law-Engine.costs_pure"></a>▫️ <a href="../../engine/core/Cost.lean#L400">Engine.costs_pure</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L195">Engine.within_pure</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.costs_tick"></a>▫️ <a href="../../engine/core/Cost.lean#L408">Engine.costs_tick</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L207">Engine.within_tick</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.work_le"></a>▫️ <a href="../../engine/core/WindowCost.lean#L43">Engine.work_le</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L351">Engine.Meter.le_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L351">Engine.Meter.le_iff</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L419">Engine.costs_ite</a></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L23">Engine.searchSteps_half</a></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L35">Engine.searchSteps_mono</a></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L47">Engine.work_add</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.costs_tick_pure"></a>▫️ <a href="../../engine/core/WindowCost.lean#L80">Engine.costs_tick_pure</a> · 7 below</summary><ul>
<li>🪜 <a href="#law-Engine.costs_bind">Engine.costs_bind</a> ↪ · 1 below · a step of Engine.decide_costs, Engine.decide_reads, Engine.find_costs +9</li>
<li>▫️ <a href="#law-Engine.costs_pure">Engine.costs_pure</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.costs_tick">Engine.costs_tick</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Cost.lean#L85">Engine.Meter.add_zero</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.costs_bind_le">Engine.costs_bind_le</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.work_le">Engine.work_le</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L47">Engine.work_add</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.costs_bind_le">Engine.costs_bind_le</a> ↪ · 6 below</li>
<li>🪜 <a href="#law-Engine.Costs.mono">Engine.Costs.mono</a> ↪ · 3 below · a step of Engine.decide_costs, Engine.decide_reads, Engine.find_costs +9</li>
<li><details><summary><a id="law-Engine.size_boundsOf_le"></a>▫️ <a href="../../engine/core/WindowCost.lean#L123">Engine.size_boundsOf_le</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L99">Engine.length_dedupSorted_le</a></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L109">Engine.length_endsOf_le</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.costs_pure">Engine.costs_pure</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.costs_tick">Engine.costs_tick</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.work_le">Engine.work_le</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Cost.lean#L351">Engine.Meter.le_iff</a></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L179">Engine.build_bounds</a></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L35">Engine.searchSteps_mono</a></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L47">Engine.work_add</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.notify_cost"></a>✅ <a href="../../engine/core/WindowCost.lean#L197">Engine.notify_cost</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.find_costs">Engine.find_costs</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Engine.val_find"></a>▫️ <a href="../../engine/core/WindowCost.lean#L185">Engine.val_find</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.val_rankM"></a>▫️ <a href="../../engine/core/WindowCost.lean#L170">Engine.val_rankM</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L451">Engine.Counted.val_bind</a></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L72">Engine.rankM_id</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowCost.lean#L163">Engine.cost_le_of_costs</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Mutants.key_notice_imprecise"></a>🧪 <a href="../../engine/core/WindowMutants.lean#L112">Engine.Mutants.key_notice_imprecise</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Mutants.window_w5"></a>▫️ <a href="../../engine/core/WindowMutants.lean#L97">Engine.Mutants.window_w5</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_window">Engine.mem_window</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.filed_iff">Engine.filed_iff</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Mutants.stepJ_hits"></a>▫️ <a href="../../engine/core/WindowMutants.lean#L81">Engine.Mutants.stepJ_hits</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_nubB">Engine.mem_nubB</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/WindowMutants.lean#L69">Engine.Mutants.stepJ_σ</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Mutants.unnetted_imprecise"></a>🧪 <a href="../../engine/core/WindowMutants.lean#L162">Engine.Mutants.unnetted_imprecise</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.Mutants.purged_empty"></a>▫️ <a href="../../engine/core/WindowMutants.lean#L136">Engine.Mutants.purged_empty</a> · 23 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_sub">Engine.closeUp_sub</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.mem_window">Engine.mem_window</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.mem_purgeS_idx">Engine.mem_purgeS_idx</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.filed_iff">Engine.filed_iff</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.mem_window">Engine.mem_window</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Mutants.stepJ_hits">Engine.Mutants.stepJ_hits</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.filed_iff">Engine.filed_iff</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-LiveLaws.agrees_notice"></a>✅ <a href="../../app/Commands.lean#L982">LiveLaws.agrees_notice</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Subs.has_keep"></a>✅ <a href="../../engine/core/WindowIndex.lean#L510">Engine.Subs.has_keep</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Subs.keep_get"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L473">Engine.Subs.keep_get</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L343">Engine.Subs.at_eq</a></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L480">Engine.Subs.filter_size_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-LiveLaws.staleAll_entries"></a>▫️ <a href="../../app/Commands.lean#L955">LiveLaws.staleAll_entries</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-LiveLaws.q_lawful">LiveLaws.q_lawful</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Subs.keep_wf"></a>✅ <a href="../../engine/core/WindowIndex.lean#L493">Engine.Subs.keep_wf</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Subs.keep_get">Engine.Subs.keep_get</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-LiveLaws.q_lawful">LiveLaws.q_lawful</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-LiveLaws.agrees_unmount"></a>✅ <a href="../../app/Commands.lean#L1025">LiveLaws.agrees_unmount</a> · 10 below</summary><ul>
<li>✅ <a href="#law-LiveLaws.agrees_keep">LiveLaws.agrees_keep</a> ↪ · 9 below</li>
<li>✅ <a href="#law-Engine.Subs.has_keep">Engine.Subs.has_keep</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-LiveLaws.watched_held"></a>✅ <a href="../../app/Commands.lean#L1036">LiveLaws.watched_held</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.Subs.has_keep">Engine.Subs.has_keep</a> ↪ · 4 below</li>
</ul></details></li>
<li><a id="law-Remove.writes_only_after_two"></a>✅ <a href="../../app/community/member/remove/View.lean#L61">Remove.writes_only_after_two</a></li>
<li><a id="law-Remove.cancel_writes_nothing"></a>✅ <a href="../../app/community/member/remove/View.lean#L67">Remove.cancel_writes_nothing</a></li>
<li><a id="law-Remove.open_fresh"></a>✅ <a href="../../app/community/member/remove/View.lean#L72">Remove.open_fresh</a></li>
<li><a id="law-Remove.no_replace"></a>✅ <a href="../../app/community/member/remove/View.lean#L79">Remove.no_replace</a></li>
<li><a id="law-Remove.offered_only"></a>✅ <a href="../../app/community/member/remove/View.lean#L88">Remove.offered_only</a></li>
<li><a id="law-Nav.back_go"></a>✅ <a href="../../engine/renderer/Nav.lean#L95">Nav.back_go</a></li>
<li><details><summary><a id="law-NavLaws.back_open"></a>✅ <a href="../../app/Proofs.lean#L1320">NavLaws.back_open</a> · 5 below</summary><ul>
<li><details><summary><a id="law-NavLaws.back_open_all"></a>✅ <a href="../../app/Proofs.lean#L1288">NavLaws.back_open_all</a> · 3 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Nav.lean#L95">Nav.back_go</a></li>
<li>✅ <a href="../../engine/renderer/Nav.lean#L89">Nav.go_page</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L1277">NavLaws.nav_open</a></li>
</ul></details></li>
<li>✅ <a href="../../app/Proofs.lean#L1312">NavLaws.open_keeps_backdrop</a></li>
</ul></details></li>
<li><details><summary><a id="law-NavLaws.back_root"></a>✅ <a href="../../app/Proofs.lean#L1331">NavLaws.back_root</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Nav.lean#L101">Nav.back_root</a></li>
</ul></details></li>
<li><details><summary><a id="law-NavLaws.back_switch"></a>✅ <a href="../../app/Proofs.lean#L1354">NavLaws.back_switch</a> · 4 below</summary><ul>
<li><details><summary><a id="law-NavLaws.backs_root"></a>▫️ <a href="../../app/Proofs.lean#L1343">NavLaws.backs_root</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Nav.lean#L101">Nav.back_root</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L1279">NavLaws.nav_back</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L1281">NavLaws.nav_switch</a></li>
</ul></details></li>
<li><details><summary><a id="law-Nav.go_inv"></a>✅ <a href="../../engine/renderer/Nav.lean#L107">Nav.go_inv</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Nav.under_inv"></a>▫️ <a href="../../engine/renderer/Nav.lean#L84">Nav.under_inv</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Nav.lean#L58">Nav.dropWhile_mem</a></li>
<li>▫️ <a href="../../engine/renderer/Nav.lean#L74">Nav.dropWhile_sublist</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-NavLaws.depth"></a>✅ <a href="../../app/Proofs.lean#L1391">NavLaws.depth</a> · 11 below</summary><ul>
<li><details><summary><a id="law-NavLaws.inv_open"></a>✅ <a href="../../app/Proofs.lean#L1368">NavLaws.inv_open</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Nav.go_inv">Nav.go_inv</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Nav.depth"></a>✅ <a href="../../engine/renderer/Nav.lean#L159">Nav.depth</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Nav.backs_stack"></a>✅ <a href="../../engine/renderer/Nav.lean#L148">Nav.backs_stack</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Nav.lean#L143">Nav.back_stack</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-NavLaws.backs_nav"></a>✅ <a href="../../app/Proofs.lean#L1381">NavLaws.backs_nav</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L1279">NavLaws.nav_back</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L1377">NavLaws.all_pages</a></li>
</ul></details></li>
<li><a id="law-NavLaws.draft_back"></a>✅ <a href="../../app/Proofs.lean#L1364">NavLaws.draft_back</a></li>
<li><details><summary><a id="law-App.into_native"></a>✅ <a href="../../app/Screen.lean#L2570">App.into_native</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Screen.lean#L2558">App.into_target</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.present_iff"></a>✅ <a href="../../app/community/Screen.lean#L397">PeopleLaws.present_iff</a> · 71 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.mem_live_all">Community.mem_live_all</a> ↪ · 68 below</li>
<li><details><summary><a id="law-PeopleLaws.byUser_mem"></a>▫️ <a href="../../app/community/Screen.lean#L387">PeopleLaws.byUser_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/reaction/View.lean#L54">RowLaws.uniq_mem</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.present_not_removed"></a>✅ <a href="../../app/community/Screen.lean#L407">PeopleLaws.present_not_removed</a> · 72 below</summary><ul>
<li>✅ <a href="#law-PeopleLaws.present_iff">PeopleLaws.present_iff</a> ↪ · 71 below</li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.present_nodup"></a>✅ <a href="../../app/community/Screen.lean#L414">PeopleLaws.present_nodup</a> · 3 below</summary><ul>
<li><details><summary><a id="law-RowLaws.uniq_nodup"></a>▫️ <a href="../../app/community/channel/message/reaction/View.lean#L64">RowLaws.uniq_nodup</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/reaction/View.lean#L54">RowLaws.uniq_mem</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.presentW_lists"></a>✅ <a href="../../app/community/Screen.lean#L663">PeopleLaws.presentW_lists</a> · 8 below</summary><ul>
<li>✅ <a href="#law-PeopleLaws.live_lists_le">PeopleLaws.live_lists_le</a> ↪ · 5 below</li>
<li>✅ <a href="#law-PeopleLaws.presentW_lists_eq">PeopleLaws.presentW_lists_eq</a> ↪ · 3 below</li>
<li>✅ <a href="../../app/community/Screen.lean#L454">PeopleLaws.all_take</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.presentW_lists_eq"></a>✅ <a href="../../app/community/Screen.lean#L644">PeopleLaws.presentW_lists_eq</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.View.listsAt_bindOp"></a>▫️ <a href="../../engine/core/ListCost.lean#L85">Engine.View.listsAt_bindOp</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/ListCost.lean#L78">Engine.View.listsAt_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/ListCost.lean#L88">Engine.View.listsAt_pure</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.present_lists_eq"></a>✅ <a href="../../app/community/Screen.lean#L652">PeopleLaws.present_lists_eq</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.View.listsAt_bindOp">Engine.View.listsAt_bindOp</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/ListCost.lean#L88">Engine.View.listsAt_pure</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.present_scans"></a>✅ <a href="../../app/community/Screen.lean#L675">PeopleLaws.present_scans</a> · 7 below</summary><ul>
<li>✅ <a href="#law-PeopleLaws.live_lists_ge">PeopleLaws.live_lists_ge</a> ↪ · 5 below</li>
<li>✅ <a href="#law-PeopleLaws.present_lists_eq">PeopleLaws.present_lists_eq</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.live_lists_le"></a>✅ <a href="../../app/community/Screen.lean#L598">PeopleLaws.live_lists_le</a> · 5 below</summary><ul>
<li>✅ <a href="#law-PeopleLaws.deviceLive_lists">PeopleLaws.deviceLive_lists</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/core/ListCost.lean#L78">Engine.View.listsAt_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.live_lists_ge"></a>✅ <a href="../../app/community/Screen.lean#L618">PeopleLaws.live_lists_ge</a> · 5 below</summary><ul>
<li>✅ <a href="#law-PeopleLaws.deviceLive_lists">PeopleLaws.deviceLive_lists</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/core/ListCost.lean#L78">Engine.View.listsAt_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-PeopleLaws.deviceLive_lists"></a>✅ <a href="../../app/community/Screen.lean#L515">PeopleLaws.deviceLive_lists</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.View.listsAt_bindOp">Engine.View.listsAt_bindOp</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/ListCost.lean#L88">Engine.View.listsAt_pure</a></li>
<li>✅ <a href="../../app/community/Screen.lean#L498">PeopleLaws.unremoved_lists</a></li>
</ul></details></li>
<li><a id="law-PeopleLaws.unremoved_lists"></a>✅ <a href="../../app/community/Screen.lean#L498">PeopleLaws.unremoved_lists</a></li>
<li><details><summary><a id="law-LiveLaws.read_one_moment"></a>✅ <a href="../../app/Commands.lean#L1043">LiveLaws.read_one_moment</a> · 16 below</summary><ul>
<li>✅ <a href="#law-LiveLaws.agrees_store">LiveLaws.agrees_store</a> ↪ · 14 below</li>
<li>✅ <a href="../../app/Commands.lean#L921">LiveLaws.answer_agrees</a></li>
</ul></details></li>
<li><a id="law-LiveLaws.answer_agrees"></a>✅ <a href="../../app/Commands.lean#L921">LiveLaws.answer_agrees</a></li>
<li><details><summary><a id="law-LiveLaws.agrees_store"></a>✅ <a href="../../app/Commands.lean#L933">LiveLaws.agrees_store</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Subs.add_wf"></a>✅ <a href="../../engine/core/WindowIndex.lean#L419">Engine.Subs.add_wf</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Subs.at_wf"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L413">Engine.Subs.at_wf</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L343">Engine.Subs.at_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Subs.set_wf"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L381">Engine.Subs.set_wf</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Subs.has_keep">Engine.Subs.has_keep</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Subs.has_add"></a>✅ <a href="../../engine/core/WindowIndex.lean#L425">Engine.Subs.has_add</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Subs.at_set"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L399">Engine.Subs.at_set</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Subs.keep_wf">Engine.Subs.keep_wf</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-LiveLaws.q_lawful">LiveLaws.q_lawful</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-LiveLaws.agrees_keep"></a>✅ <a href="../../app/Commands.lean#L1012">LiveLaws.agrees_keep</a> · 9 below</summary><ul>
<li>✅ <a href="#law-Engine.Subs.has_keep">Engine.Subs.has_keep</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Engine.Subs.keep_wf">Engine.Subs.keep_wf</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-LiveLaws.q_lawful">LiveLaws.q_lawful</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-LiveLaws.agrees_empty"></a>✅ <a href="../../app/Commands.lean#L917">LiveLaws.agrees_empty</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-LiveLaws.q_lawful">LiveLaws.q_lawful</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Subs.wf_empty"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L340">Engine.Subs.wf_empty</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Cover.covered"></a>✅ <a href="../../engine/renderer/Cover.lean#L84">Cover.covered</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Cover.lean#L70">Cover.find_blank</a></li>
<li>▫️ <a href="../../engine/renderer/Cover.lean#L55">Cover.find_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Cover.line_painted"></a>✅ <a href="../../engine/renderer/Cover.lean#L124">Cover.line_painted</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Cover.lean#L101">Cover.find_line</a></li>
</ul></details></li>
<li><details><summary><a id="law-Translate.covered"></a>✅ <a href="../../engine/renderer/TranslateLaws.lean#L83">Translate.covered</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Cover.covered">Cover.covered</a> ↪ · 2 below</li>
</ul></details></li>
<li><a id="law-Translate.equivariance"></a>✅ <a href="../../engine/renderer/TranslateLaws.lean#L12">Translate.equivariance</a></li>
<li><details><summary><a id="law-Translate.fill_pixel"></a>✅ <a href="../../engine/renderer/TranslateLaws.lean#L144">Translate.fill_pixel</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Translate.tile_phase"></a>🪜 <a href="../../engine/renderer/TranslateLaws.lean#L58">Translate.tile_phase</a> · 1 below · a step of Translate.fill_pixel</summary><ul>
<li>🪜 <a href="../../engine/renderer/TranslateLaws.lean#L48">Translate.fill_index</a> · a step of Translate.fill_pixel</li>
</ul></details></li>
<li>🪜 <a href="../../engine/renderer/TranslateLaws.lean#L48">Translate.fill_index</a> · a step of Translate.fill_pixel</li>
<li>✅ <a href="../../engine/renderer/TranslateLaws.lean#L139">Translate.hold_row</a></li>
</ul></details></li>
<li><details><summary><a id="law-Slide.edge_eq"></a>✅ <a href="../../engine/renderer/SlideLaws.lean#L127">Slide.edge_eq</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Slide.crop_eq"></a>▫️ <a href="../../engine/renderer/SlideLaws.lean#L92">Slide.crop_eq</a> · 5 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L7">Slide.add_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L31">Slide.high_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L27">Slide.low_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L19">Slide.sub32_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L11">Slide.sub_nat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Slide.fill_val"></a>▫️ <a href="../../engine/renderer/SlideLaws.lean#L65">Slide.fill_val</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Slide.lift_val"></a>▫️ <a href="../../engine/renderer/SlideLaws.lean#L42">Slide.lift_val</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L35">Slide.signed_val</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L7">Slide.add_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L11">Slide.sub_nat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Slide.position_val"></a>▫️ <a href="../../engine/renderer/SlideLaws.lean#L48">Slide.position_val</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Slide.lift_val">Slide.lift_val</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L7">Slide.add_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L11">Slide.sub_nat</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L7">Slide.add_nat</a></li>
<li>▫️ <a href="../../engine/renderer/SlideLaws.lean#L11">Slide.sub_nat</a></li>
</ul></details></li>
<li><details><summary><a id="law-PlaceLaws.bottoms_eq"></a>✅ <a href="../../app/Proofs.lean#L4182">PlaceLaws.bottoms_eq</a> · 3 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L4165">PlaceLaws.bots_get</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L4174">PlaceLaws.bots_length</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L4152">PlaceLaws.foldl_bots</a></li>
</ul></details></li>
<li><details><summary><a id="law-PlaceLaws.rowAt_iff"></a>✅ <a href="../../app/Proofs.lean#L4253">PlaceLaws.rowAt_iff</a> · 5 below</summary><ul>
<li>✅ <a href="#law-PlaceLaws.bottoms_eq">PlaceLaws.bottoms_eq</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L4203">PlaceLaws.rowFrom_iff</a></li>
</ul></details></li>
<li><a id="law-Hold.messageLine_key"></a>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L6">Hold.messageLine_key</a></li>
<li><a id="law-Hold.prepare_key"></a>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L9">Hold.prepare_key</a></li>
<li><a id="law-Hold.prepare_reuses"></a>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L17">Hold.prepare_reuses</a></li>
<li><details><summary><a id="law-Hold.prepare_rows"></a>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L22">Hold.prepare_rows</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L9">Hold.prepare_key</a></li>
</ul></details></li>
<li><details><summary><a id="law-Hold.cachedMessagePlane_exact"></a>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L28">Hold.cachedMessagePlane_exact</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Hold.prepare_rows">Hold.prepare_rows</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L9">Hold.prepare_key</a></li>
</ul></details></li>
<li><details><summary><a id="law-Hold.cachedMessagePlane_reuses"></a>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L35">Hold.cachedMessagePlane_reuses</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L9">Hold.prepare_key</a></li>
<li>✅ <a href="../../engine/renderer/HoldCacheLaws.lean#L17">Hold.prepare_reuses</a></li>
</ul></details></li>
<li><details><summary><a id="law-Surface.placed_row"></a>✅ <a href="../../engine/renderer/Surface.lean#L119">Surface.placed_row</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Geometry.placed_row">Geometry.placed_row</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/renderer/Surface.lean#L111">Surface.row_place</a></li>
</ul></details></li>
<li><details><summary><a id="law-Surface.newest_drawn"></a>✅ <a href="../../engine/renderer/Surface.lean#L146">Surface.newest_drawn</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Geometry.newest_drawn"></a>✅ <a href="../../engine/renderer/Geometry.lean#L111">Geometry.newest_drawn</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Geometry.placed_row">Geometry.placed_row</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/renderer/Geometry.lean#L95">Geometry.visible_in_viewport</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/renderer/Surface.lean#L111">Surface.row_place</a></li>
</ul></details></li>
<li><details><summary><a id="law-Surface.pinned_row"></a>✅ <a href="../../engine/renderer/Surface.lean#L137">Surface.pinned_row</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Geometry.lean#L145">Geometry.pinned_row</a></li>
<li>✅ <a href="../../engine/renderer/Surface.lean#L115">Surface.row_pinned</a></li>
</ul></details></li>
<li><details><summary><a id="law-SheetGeom.keys_disjoint"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L180">SheetGeom.keys_disjoint</a> · 4 below</summary><ul>
<li>✅ <a href="#law-SheetGeom.hit_cell">SheetGeom.hit_cell</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-SheetGeom.hit_cell"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L176">SheetGeom.hit_cell</a> · 3 below</summary><ul>
<li>✅ <a href="#law-SheetGeom.hit_iff">SheetGeom.hit_iff</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-SheetGeom.reachable"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L198">SheetGeom.reachable</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/SheetGeom.lean#L188">SheetGeom.row_lt</a></li>
</ul></details></li>
<li><a id="law-SheetGeom.itemAt_place"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L89">SheetGeom.itemAt_place</a></li>
<li><a id="law-SheetGeom.lineOf_ctop"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L100">SheetGeom.lineOf_ctop</a></li>
<li><a id="law-Composer.chips_apart"></a>✅ <a href="../../app/community/channel/message/draft/View.lean#L100">Composer.chips_apart</a></li>
<li><details><summary><a id="law-Composer.x_clear"></a>✅ <a href="../../app/community/channel/message/draft/View.lean#L109">Composer.x_clear</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/draft/View.lean#L94">Composer.px_mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Composer.chips_fit"></a>✅ <a href="../../app/community/channel/message/draft/View.lean#L120">Composer.chips_fit</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/draft/View.lean#L94">Composer.px_mono</a></li>
</ul></details></li>
<li><a id="law-SheetGeom.compose_row"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L222">SheetGeom.compose_row</a></li>
<li><a id="law-SheetGeom.compose_top"></a>✅ <a href="../../engine/renderer/SheetGeom.lean#L231">SheetGeom.compose_top</a></li>
<li><a id="law-Link.hints_fit"></a>✅ <a href="../../app/community/member/invite/View.lean#L39">Link.hints_fit</a></li>
<li><a id="law-Link.qr_fits"></a>✅ <a href="../../app/community/member/invite/View.lean#L56">Link.qr_fits</a></li>
<li><details><summary><a id="law-Camera.src_in"></a>✅ <a href="../../engine/renderer/Camera.lean#L52">Camera.src_in</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Camera.lean#L46">Camera.scaled_lt</a></li>
</ul></details></li>
<li><details><summary><a id="law-Text.wrap_keeps"></a>✅ <a href="../../engine/renderer/WrapLaws.lean#L134">Text.wrap_keeps</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Text.fill_keeps"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L102">Text.fill_keeps</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Text.breakIn_keeps"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L82">Text.breakIn_keeps</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Text.trimEnd_filter"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L47">Text.trimEnd_filter</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L40">Text.dropWhile_sp_filter</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L50">Text.trimEnd_sublist</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Text.trimEnd_filter">Text.trimEnd_filter</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L50">Text.trimEnd_sublist</a></li>
</ul></details></li>
<li><details><summary><a id="law-Text.tokens_flatten"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L18">Text.tokens_flatten</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/Text.lean#L119">Text.splitW_append</a></li>
<li>▫️ <a href="../../engine/renderer/Text.lean#L123">Text.splitW_len</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Text.wrap_fits"></a>✅ <a href="../../engine/renderer/WrapLaws.lean#L208">Text.wrap_fits</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Text.fill_fits"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L174">Text.fill_fits</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Text.breakIn_fits"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L142">Text.breakIn_fits</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Text.trimEnd_le"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L62">Text.trimEnd_le</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L57">Text.lineW_sublist</a></li>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L50">Text.trimEnd_sublist</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L54">Text.lineW_append</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Text.trimEnd_le">Text.trimEnd_le</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Text.trimEnd_spaces"></a>▫️ <a href="../../engine/renderer/WrapLaws.lean#L72">Text.trimEnd_spaces</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L65">Text.dropWhile_spaces_append</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/WrapLaws.lean#L54">Text.lineW_append</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Text.tokens_flatten">Text.tokens_flatten</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Text.visual_perm"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L21">Text.visual_perm</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Text.Bidi.display_perm"></a>✅ <a href="../../engine/renderer/bidi/Laws.lean#L79">Text.Bidi.display_perm</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Text.Bidi.weak_keeps"></a>✅ <a href="../../engine/renderer/bidi/Laws.lean#L36">Text.Bidi.weak_keeps</a> · 4 below</summary><ul>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L30">Text.Bidi.et_keeps</a></li>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L12">Text.Bidi.w1_keeps</a></li>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L18">Text.Bidi.w23_keeps</a></li>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L24">Text.Bidi.w4_keeps</a></li>
</ul></details></li>
<li><details><summary><a id="law-Text.Bidi.leveled_keeps"></a>✅ <a href="../../engine/renderer/bidi/Laws.lean#L63">Text.Bidi.leveled_keeps</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L51">Text.Bidi.attach_keeps</a></li>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L57">Text.Bidi.reset_keeps</a></li>
</ul></details></li>
<li><details><summary><a id="law-Text.Bidi.reorder_perm"></a>✅ <a href="../../engine/renderer/bidi/Laws.lean#L76">Text.Bidi.reorder_perm</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L67">Text.Bidi.reverseRuns_perm</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/renderer/bidi/Laws.lean#L40">Text.Bidi.runs_keeps</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Text.place_shows"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L37">Text.place_shows</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/TextLaws.lean#L25">Text.placeL_shows</a></li>
</ul></details></li>
<li><a id="law-Text.place_starts"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L119">Text.place_starts</a></li>
<li><details><summary><a id="law-Text.numbers_keep_order"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L87">Text.numbers_keep_order</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Text.Bidi.run_contiguous"></a>🪜 <a href="../../engine/renderer/bidi/Laws.lean#L86">Text.Bidi.run_contiguous</a> · 5 below · a step of Text.arabic_numbers_keep_order, Text.numbers_keep_order</summary><ul>
<li>✅ <a href="#law-Text.Bidi.leveled_keeps">Text.Bidi.leveled_keeps</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Text.Bidi.reorder_perm">Text.Bidi.reorder_perm</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Text.arabic_numbers_keep_order"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L93">Text.arabic_numbers_keep_order</a> · 6 below</summary><ul>
<li>🪜 <a href="#law-Text.Bidi.run_contiguous">Text.Bidi.run_contiguous</a> ↪ · 5 below · a step of Text.arabic_numbers_keep_order, Text.numbers_keep_order</li>
</ul></details></li>
<li><a id="law-ViewLaws.profile_read"></a>✅ <a href="../../app/community/Screen.lean#L83">ViewLaws.profile_read</a></li>
<li><details><summary><a id="law-Community.profile_authorized"></a>✅ <a href="../../app/community/profile/Proofs.lean#L29">Community.profile_authorized</a> · 46 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_profile"></a>▫️ <a href="../../app/community/profile/Proofs.lean#L6">Community.check_profile</a> · 31 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1296">Community.all2_two</a></li>
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
<li><details><summary><a id="law-Community.no_renaming"></a>✅ <a href="../../app/community/Proofs.lean#L138">Community.no_renaming</a> · 51 below</summary><ul>
<li>🪜 <a href="security-proofs-identity-and-membership.md#law-Community.admission_consented">Community.admission_consented</a> ↪ · 47 below · a step of Community.no_impersonation, Community.no_renaming</li>
<li>✅ <a href="#law-Community.profile_authorized">Community.profile_authorized</a> ↪ · 46 below</li>
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
<li><a id="law-RowLaws.name_placed"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L82">RowLaws.name_placed</a></li>
<li><details><summary><a id="law-Text.oneLine_prefix"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L70">Text.oneLine_prefix</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Text.oneLinePlaced_prefix"></a>▫️ <a href="../../engine/renderer/TextLaws.lean#L51">Text.oneLinePlaced_prefix</a> · 15 below</summary><ul>
<li>✅ <a href="#law-Text.visual_perm">Text.visual_perm</a> ↪ · 12 below</li>
<li>✅ <a href="#law-Text.place_shows">Text.place_shows</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/TextLaws.lean#L44">Text.shown_shift</a></li>
</ul></details></li>
<li><a id="law-Text.controls_neutral"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L143">Text.controls_neutral</a></li>
<li><a id="law-Text.marks_invisible"></a>✅ <a href="../../engine/renderer/TextLaws.lean#L145">Text.marks_invisible</a></li>
<li><details><summary><a id="law-ViewLaws.namesake_iff"></a>✅ <a href="../../app/community/Screen.lean#L234">ViewLaws.namesake_iff</a> · 64 below</summary><ul>
<li><details><summary><a id="law-ViewLaws.newest"></a>▫️ <a href="../../app/community/profile/View.lean#L84">ViewLaws.newest</a> · 60 below</summary><ul>
<li><details><summary><a id="law-Community.at_row"></a>▫️ <a href="../../app/community/Family.lean#L1592">Community.at_row</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1538">Community.matching_also_nil</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1557">Community.mem_eval_all</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Community.row_filed">Community.row_filed</a> ↪ · 55 below</li>
<li>▫️ <a href="../../app/community/profile/View.lean#L66">ViewLaws.byUser_args</a></li>
<li>▫️ <a href="../../app/community/profile/View.lean#L62">ViewLaws.eval_one</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.at_row">Community.at_row</a> ↪ · 55 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Community.row_filed">Community.row_filed</a> ↪ · 55 below</li>
<li><details><summary><a id="law-ViewLaws.others_iff"></a>✅ <a href="../../app/community/Screen.lean#L179">ViewLaws.others_iff</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/community/Screen.lean#L83">ViewLaws.profile_read</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/profile/View.lean#L70">ViewLaws.byLook_args</a></li>
</ul></details></li>
<li><details><summary><a id="law-ViewLaws.row_marked"></a>✅ <a href="../../app/community/Screen.lean#L262">ViewLaws.row_marked</a> · 65 below</summary><ul>
<li>✅ <a href="#law-ViewLaws.namesake_iff">ViewLaws.namesake_iff</a> ↪ · 64 below</li>
<li>✅ <a href="../../app/community/Screen.lean#L83">ViewLaws.profile_read</a></li>
</ul></details></li>
<li><a id="law-RowLaws.twin_shown"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L132">RowLaws.twin_shown</a></li>
<li><a id="law-RowLaws.twin_before_time"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L138">RowLaws.twin_before_time</a></li>
<li><a id="law-RowLaws.hit_twin"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L151">RowLaws.hit_twin</a></li>
<li><details><summary><a id="law-RowLaws.name_starts"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L116">RowLaws.name_starts</a> · 2 below</summary><ul>
<li>✅ <a href="../../app/community/channel/message/reaction/View.lean#L95">RowLaws.flush_start</a></li>
<li>✅ <a href="../../app/community/channel/message/reaction/View.lean#L82">RowLaws.name_placed</a></li>
</ul></details></li>
<li><a id="law-RowLaws.flush_shows"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L90">RowLaws.flush_shows</a></li>
<li><a id="law-Ttf.byte_in_bounds"></a>✅ <a href="../../engine/renderer/Ttf/Laws.lean#L11">Ttf.byte_in_bounds</a></li>
<li><a id="law-Ttf.cmap_entry"></a>✅ <a href="../../engine/renderer/Ttf/Laws.lean#L18">Ttf.cmap_entry</a></li>
<li><a id="law-Ttf.coverage_value"></a>✅ <a href="../../engine/renderer/Ttf/Laws.lean#L44">Ttf.coverage_value</a></li>
<li><details><summary><a id="law-Ttf.raster_valid"></a>✅ <a href="../../engine/renderer/Ttf/Laws.lean#L60">Ttf.raster_valid</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Ttf/Laws.lean#L54">Ttf.checked_valid</a></li>
</ul></details></li>
<li><details><summary><a id="law-Ttf.raster_pixel"></a>✅ <a href="../../engine/renderer/Ttf/Laws.lean#L71">Ttf.raster_pixel</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Ttf.raster_valid">Ttf.raster_valid</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Ttf.Memo.bitmap_eq_fast"></a>✅ <a href="../../engine/renderer/Ttf/Memo.lean#L112">Ttf.Memo.bitmap_eq_fast</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Ttf/Memo.lean#L47">Ttf.Memo.Table.get_eq</a></li>
<li>✅ <a href="../../engine/renderer/Ttf/Memo.lean#L61">Ttf.Memo.compact_eq</a></li>
</ul></details></li>
<li><a id="law-Ttf.Memo.Table.get_eq"></a>✅ <a href="../../engine/renderer/Ttf/Memo.lean#L47">Ttf.Memo.Table.get_eq</a></li>
<li><a id="law-RowLaws.time_shown"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L76">RowLaws.time_shown</a></li>
<li><a id="law-Data.projectSet_mem"></a>✅ <a href="../../app/Commands.lean#L796">Data.projectSet_mem</a></li>
<li><details><summary><a id="law-Data.projectSet_nodup"></a>✅ <a href="../../app/Commands.lean#L811">Data.projectSet_nodup</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Commands.lean#L801">Data.set_nodup</a></li>
</ul></details></li>
<li><a id="law-RowLaws.picBox_aspect"></a>✅ <a href="../../app/community/channel/message/reaction/View.lean#L41">RowLaws.picBox_aspect</a></li>
<li><details><summary><a id="law-ArrivalLaws.ring_counts"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L260">ArrivalLaws.ring_counts</a> · 7 below</summary><ul>
<li><details><summary><a id="law-ArrivalLaws.layout_words"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L210">ArrivalLaws.layout_words</a> · 6 below</summary><ul>
<li><details><summary><a id="law-ArrivalLaws.layout_arriving"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L191">ArrivalLaws.layout_arriving</a> · 2 below</summary><ul>
<li>✅ <a href="../../app/community/channel/message/attachment/View.lean#L41">ArrivalLaws.caption_none_iff</a></li>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L115">ArrivalLaws.layout_spec</a></li>
</ul></details></li>
<li><details><summary><a id="law-ArrivalLaws.pick_spec"></a>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L145">ArrivalLaws.pick_spec</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L137">ArrivalLaws.fit_spec</a></li>
</ul></details></li>
<li>✅ <a href="../../app/community/channel/message/attachment/View.lean#L46">ArrivalLaws.caption_some</a></li>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L137">ArrivalLaws.fit_spec</a></li>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L115">ArrivalLaws.layout_spec</a></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-ArrivalLaws.lit_zero"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L70">ArrivalLaws.lit_zero</a></li>
<li><details><summary><a id="law-ArrivalLaws.lit_full"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L80">ArrivalLaws.lit_full</a> · 3 below</summary><ul>
<li><details><summary><a id="law-ArrivalLaws.turn_lt"></a>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L60">ArrivalLaws.turn_lt</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L53">ArrivalLaws.off_pos</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L65">ArrivalLaws.arc_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-ArrivalLaws.lit_mono"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L74">ArrivalLaws.lit_mono</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L65">ArrivalLaws.arc_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-ArrivalLaws.lit_clockwise"></a>✅ <a href="../../app/community/channel/message/attachment/View.lean#L88">ArrivalLaws.lit_clockwise</a> · 3 below</summary><ul>
<li><details><summary><a id="law-ArrivalLaws.turn_pos"></a>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L55">ArrivalLaws.turn_pos</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L53">ArrivalLaws.off_pos</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/channel/message/attachment/View.lean#L65">ArrivalLaws.arc_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-ViewLaws.message_own"></a>✅ <a href="../../app/community/Screen.lean#L100">ViewLaws.message_own</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/View.lean#L19">ViewLaws.pure_none_ne</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.readable_held"></a>✅ <a href="../../app/community/Proofs.lean#L410">Community.readable_held</a> · 82 below</summary><ul>
<li><details><summary><a id="law-Community.heldKids_held"></a>▫️ <a href="../../app/community/Proofs.lean#L372">Community.heldKids_held</a> · 57 below</summary><ul>
<li><details><summary><a id="law-Community.row_at"></a>▫️ <a href="../../app/community/Family.lean#L1582">Community.row_at</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1538">Community.matching_also_nil</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1542">Community.mem_eval_matching</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.row_at">Community.row_at</a> ↪ · 55 below</li>
<li><details><summary><a id="law-Community.received_of_message"></a>✅ <a href="../../app/community/channel/message/receipt/Proofs.lean#L29">Community.received_of_message</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/channel/message/receipt/Proofs.lean#L10">Community.check_received</a></li>
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
<li><details><summary><a id="law-Engine.mem_union"></a>✅ <a href="../../engine/core/Union.lean#L150">Engine.mem_union</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_mergeRuns_orient"></a>✅ <a href="../../engine/core/Union.lean#L139">Engine.mem_mergeRuns_orient</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/core/Union.lean#L71">Engine.mem_orient</a></li>
<li>✅ <a href="../../engine/core/Union.lean#L65">Engine.perm_mergeRuns</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.eval_readable"></a>▫️ <a href="../../app/community/Proofs.lean#L393">Community.eval_readable</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.eval_readAll"></a>▫️ <a href="../../engine/core/Union.lean#L200">Engine.eval_readAll</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.readable_complete"></a>✅ <a href="../../app/community/Proofs.lean#L449">Community.readable_complete</a> · 64 below</summary><ul>
<li><details><summary><a id="law-Community.held_heldKids"></a>▫️ <a href="../../app/community/Proofs.lean#L386">Community.held_heldKids</a> · 57 below</summary><ul>
<li>▫️ <a href="#law-Community.at_row">Community.at_row</a> ↪ · 55 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.at_row">Community.at_row</a> ↪ · 55 below</li>
<li><details><summary><a id="law-Engine.mem_union_all"></a>✅ <a href="../../engine/core/Union.lean#L159">Engine.mem_union_all</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Engine.mem_mergeRuns_orient">Engine.mem_mergeRuns_orient</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Community.eval_readable">Community.eval_readable</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Pages.switcherOrder_sound"></a>✅ <a href="../../app/community/Screen.lean#L1048">Pages.switcherOrder_sound</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Screen.lean#L1041">Pages.ix_sound</a></li>
</ul></details></li>
<li><a id="law-Pages.switcherOrder_complete"></a>✅ <a href="../../app/community/Screen.lean#L1055">Pages.switcherOrder_complete</a></li>
<li><details><summary><a id="law-Switch.dedupe_nodup"></a>✅ <a href="../../app/community/Screen.lean#L738">Switch.dedupe_nodup</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Switch.dedupeBy_nodup"></a>▫️ <a href="../../app/community/Screen.lean#L716">Switch.dedupeBy_nodup</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Screen.lean#L703">Switch.dedupeBy_fresh</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Switch.dedupe_one_per_community"></a>✅ <a href="../../app/community/Screen.lean#L743">Switch.dedupe_one_per_community</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Switch.dedupeBy_nodup">Switch.dedupeBy_nodup</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Screen.lean#L728">Switch.dedupeBy_sublist</a></li>
</ul></details></li>
<li><details><summary><a id="law-Switch.select_tapped_dedupe"></a>✅ <a href="../../app/community/Screen.lean#L768">Switch.select_tapped_dedupe</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Switch.dedupe_nodup">Switch.dedupe_nodup</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Switch.select_tapped"></a>✅ <a href="../../app/community/Screen.lean#L760">Switch.select_tapped</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Screen.lean#L748">Switch.find_nodup</a></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-App.drawPage_key"></a>✅ <a href="../../app/Screen.lean#L4335">App.drawPage_key</a></li>
<li><a id="law-App.pageIn_acc"></a>✅ <a href="../../app/Screen.lean#L4363">App.pageIn_acc</a></li>
<li><details><summary><a id="law-Community.msg_cmp"></a>✅ <a href="../../app/community/channel/message/Proofs.lean#L121">Community.msg_cmp</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Community.bcmp_msgKey"></a>▫️ <a href="../../app/community/channel/message/Proofs.lean#L110">Community.bcmp_msgKey</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Community.lexCmp_be64"></a>✅ <a href="../../app/community/Family.lean#L1739">Community.lexCmp_be64</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.lexCmp_digits"></a>▫️ <a href="../../app/community/Family.lean#L1707">Community.lexCmp_digits</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/community/Family.lean#L1690">Community.compare_place</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1685">Community.digit_toNat</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1730">Community.be64_toList</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Community.be64_len_eq"></a>▫️ <a href="../../app/community/Family.lean#L1735">Community.be64_len_eq</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Community.be64_length"></a>▫️ <a href="../../app/community/Family.lean#L1732">Community.be64_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Family.lean#L1730">Community.be64_toList</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1747">Community.countCap_lt</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1749">Community.min_lt</a></li>
<li>▫️ <a href="../../app/community/channel/message/Proofs.lean#L108">Community.timeCap_lt</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1744">Community.toList_append</a></li>
<li>▫️ <a href="../../engine/core/Order.lean#L22">Engine.lexCmp_append</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.time_is_display"></a>✅ <a href="../../app/community/channel/message/Proofs.lean#L131">Community.time_is_display</a> · 18 below</summary><ul>
<li>✅ <a href="#law-Community.msg_cmp">Community.msg_cmp</a> ↪ · 17 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.order_total"></a>✅ <a href="../../app/community/Proofs.lean#L1506">Community.order_total</a> · 102 below</summary><ul>
<li><details><summary><a id="law-Community.asMsg_sorted"></a>✅ <a href="../../app/community/Proofs.lean#L1469">Community.asMsg_sorted</a> · 85 below</summary><ul>
<li>▫️ <a href="#law-Community.row_at">Community.row_at</a> ↪ · 55 below</li>
<li><details><summary><a id="law-Engine.eval_oriented"></a>✅ <a href="../../engine/core/Union.lean#L223">Engine.eval_oriented</a> · 19 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.sortPos_eq_fast">Engine.sortPos_eq_fast</a> ↪ · 17 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.posLE_trans">Engine.posLE_trans</a> ↪ · 13 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.posLE_total">Engine.posLE_total</a> ↪ · 8 below</li>
<li>✅ <a href="../../engine/core/Union.lean#L208">Engine.eval_pairwise</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_eq_iff"></a>▫️ <a href="../../engine/core/Order.lean#L36">Engine.bcmp_eq_iff</a> · 7 below</summary><ul>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Order.lean#L14">Engine.lexCmp_self</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Community.recKey_inj"></a>✅ <a href="../../app/community/channel/message/receipt/Proofs.lean#L61">Community.recKey_inj</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Community.be64_length">Community.be64_length</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Community.recKey_toList"></a>▫️ <a href="../../app/community/channel/message/receipt/Proofs.lean#L42">Community.recKey_toList</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Family.lean#L1744">Community.toList_append</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="../../app/community/Family.lean#L1752">Community.orient_map</a></li>
<li>✅ <a href="../../engine/core/Union.lean#L71">Engine.mem_orient</a></li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.union_sorted"></a>✅ <a href="../../engine/core/Union.lean#L189">Engine.union_sorted</a> · 26 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.union_rows">Engine.union_rows</a> ↪ · 20 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.sortPos_eq_fast">Engine.sortPos_eq_fast</a> ↪ · 17 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.posLE_trans">Engine.posLE_trans</a> ↪ · 13 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.posLE_total">Engine.posLE_total</a> ↪ · 8 below</li>
<li>✅ <a href="../../engine/core/Union.lean#L177">Engine.pairwise_orient_cut</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.eval_oriented">Engine.eval_oriented</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.strict_of">Engine.strict_of</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Community.eval_readable">Community.eval_readable</a> ↪ · 2 below</li>
<li>✅ <a href="../../app/community/channel/message/Proofs.lean#L148">Community.orient_orient</a></li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.cmp_eq_iff"></a>✅ <a href="../../engine/core/Order.lean#L46">Engine.Pos.cmp_eq_iff</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq_iff">Engine.bcmp_eq_iff</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/Order.lean#L39">Engine.then_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.cmp_lt_trans"></a>✅ <a href="../../engine/core/Order.lean#L58">Engine.Pos.cmp_lt_trans</a> · 18 below</summary><ul>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.strict_of">Engine.strict_of</a> ↪ · 10 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.send_after"></a>✅ <a href="../../app/community/Proofs.lean#L1691">Community.send_after</a> · 120 below</summary><ul>
<li><details><summary><a id="law-Community.receipt_past"></a>▫️ <a href="../../app/community/Proofs.lean#L1588">Community.receipt_past</a> · 92 below</summary><ul>
<li><details><summary><a id="law-Community.topReceived_ge"></a>▫️ <a href="../../app/community/Proofs.lean#L1562">Community.topReceived_ge</a> · 89 below</summary><ul>
<li><details><summary><a id="law-Community.first_after"></a>▫️ <a href="../../app/community/Family.lean#L1761">Community.first_after</a> · 75 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.top_max">Engine.top_max</a> ↪ · 21 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1538">Community.matching_also_nil</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.bcmp_recKey"></a>▫️ <a href="../../app/community/channel/message/receipt/Proofs.lean#L46">Community.bcmp_recKey</a> · 15 below</summary><ul>
<li>✅ <a href="#law-Community.lexCmp_be64">Community.lexCmp_be64</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Community.be64_len_eq">Community.be64_len_eq</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Community.recKey_toList">Community.recKey_toList</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1747">Community.countCap_lt</a></li>
<li>▫️ <a href="../../engine/core/Order.lean#L22">Engine.lexCmp_append</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.row_at">Community.row_at</a> ↪ · 55 below</li>
<li>▫️ <a href="#law-Community.bcmp_recKey">Community.bcmp_recKey</a> ↪ · 15 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.topCount_ge"></a>✅ <a href="../../app/community/Proofs.lean#L1545">Community.topCount_ge</a> · 91 below</summary><ul>
<li>▫️ <a href="#law-Community.first_after">Community.first_after</a> ↪ · 75 below</li>
<li>✅ <a href="#law-Community.msg_cmp">Community.msg_cmp</a> ↪ · 17 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.receipt_post"></a>▫️ <a href="../../app/community/Proofs.lean#L1635">Community.receipt_post</a> · 73 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>✅ <a href="#law-Community.received_of_message">Community.received_of_message</a> ↪ · 45 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1538">Community.matching_also_nil</a></li>
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
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>✅ <a href="#law-Community.received_of_message">Community.received_of_message</a> ↪ · 45 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
<li>✅ <a href="#law-Community.time_is_display">Community.time_is_display</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Community.bcmp_msg_rec"></a>▫️ <a href="../../app/community/channel/message/receipt/Proofs.lean#L54">Community.bcmp_msg_rec</a> · 16 below</summary><ul>
<li>✅ <a href="#law-Community.lexCmp_be64">Community.lexCmp_be64</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Community.be64_len_eq">Community.be64_len_eq</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Community.recKey_toList">Community.recKey_toList</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1747">Community.countCap_lt</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1749">Community.min_lt</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1744">Community.toList_append</a></li>
<li>▫️ <a href="../../engine/core/Order.lean#L22">Engine.lexCmp_append</a></li>
</ul></details></li>
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
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.arrival_order"></a>✅ <a href="../../app/community/Proofs.lean#L1663">Community.arrival_order</a> · 105 below</summary><ul>
<li>▫️ <a href="#law-Community.receipt_past">Community.receipt_past</a> ↪ · 92 below</li>
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
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.receipt_once"></a>✅ <a href="../../app/community/Proofs.lean#L1614">Community.receipt_once</a> · 67 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1538">Community.matching_also_nil</a></li>
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
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-connections.md#law-Community.order_local">Community.order_local</a> ↪ · 65 below</li>
<li><details><summary><a id="law-Community.display_agrees"></a>✅ <a href="../../app/community/channel/message/Proofs.lean#L202">Community.display_agrees</a> · 73 below</summary><ul>
<li><details><summary><a id="law-Community.listed_cases"></a>▫️ <a href="../../app/community/channel/message/Proofs.lean#L187">Community.listed_cases</a> · 51 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.message_authorized">Community.message_authorized</a> ↪ · 48 below</li>
<li>✅ <a href="#law-Community.received_of_message">Community.received_of_message</a> ↪ · 45 below</li>
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
<li><details><summary><a id="law-Community.posted_unique"></a>▫️ <a href="../../app/community/channel/message/Proofs.lean#L177">Community.posted_unique</a> · 40 below</summary><ul>
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
<li>▫️ <a href="#law-Community.bcmp_msg_rec">Community.bcmp_msg_rec</a> ↪ · 16 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
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
<li><details><summary><a id="law-Notify.step_post"></a>✅ <a href="../../app/community/Screen.lean#L1532">Notify.step_post</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Notify.step_fold_post"></a>▫️ <a href="../../app/community/Screen.lean#L1468">Notify.step_fold_post</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Notify.arriveAll_post"></a>▫️ <a href="../../app/community/Screen.lean#L1438">Notify.arriveAll_post</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Screen.lean#L1419">Notify.arrive_post</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="../../app/community/Screen.lean#L1398">Notify.notifies_iff</a></li>
</ul></details></li>
<li><a id="law-Notify.notifies_iff"></a>✅ <a href="../../app/community/Screen.lean#L1398">Notify.notifies_iff</a></li>
<li><a id="law-Notify.own_silent"></a>✅ <a href="../../app/community/Screen.lean#L1395">Notify.own_silent</a></li>
<li><a id="law-Notify.can_alert"></a>✅ <a href="../../app/community/Screen.lean#L1402">Notify.can_alert</a></li>
<li><a id="law-Notify.once"></a>✅ <a href="../../app/community/Screen.lean#L1404">Notify.once</a></li>
<li><details><summary><a id="law-Notify.step_quiet"></a>✅ <a href="../../app/community/Screen.lean#L1484">Notify.step_quiet</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Notify.step_fold_post">Notify.step_fold_post</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Notify.step_read"></a>✅ <a href="../../app/community/Screen.lean#L1515">Notify.step_read</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Notify.step_removed"></a>✅ <a href="../../app/community/Screen.lean#L1502">Notify.step_removed</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Notify.step_keeps"></a>✅ <a href="../../app/community/Screen.lean#L1524">Notify.step_keeps</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Notify.step_fold_active"></a>▫️ <a href="../../app/community/Screen.lean#L1462">Notify.step_fold_active</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Notify.arriveAll_active"></a>▫️ <a href="../../app/community/Screen.lean#L1427">Notify.arriveAll_active</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Screen.lean#L1411">Notify.arrive_active</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Notify.marks_le"></a>✅ <a href="../../app/community/Screen.lean#L1544">Notify.marks_le</a></li>
<li><details><summary><a id="law-Community.target_roundtrip"></a>✅ <a href="../../app/community/Proofs.lean#L1865">Community.target_roundtrip</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>✅ <a href="quality-proofs-codes-pictures-and-discovery.md#law-Community.Base62.decode_encode">Community.Base62.decode_encode</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1832">Community.openScheme_prefix</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-App.target_opens"></a>✅ <a href="../../app/Proofs.lean#L4019">App.target_opens</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/Nav.lean#L89">Nav.go_page</a></li>
</ul></details></li>
<li><a id="law-App.targetOf_member"></a>✅ <a href="../../app/Proofs.lean#L4028">App.targetOf_member</a></li>
<li><a id="law-App.syncs_kept"></a>✅ <a href="../../app/Proofs.lean#L3989">App.syncs_kept</a></li>
<li><a id="law-App.syncs_off"></a>✅ <a href="../../app/Proofs.lean#L3993">App.syncs_off</a></li>
<li><a id="law-App.keepSync_keeps"></a>✅ <a href="../../app/Proofs.lean#L3998">App.keepSync_keeps</a></li>
<li><a id="law-App.keepSync_set"></a>✅ <a href="../../app/Proofs.lean#L4004">App.keepSync_set</a></li>
<li><a id="law-App.unmount_keeps_node"></a>✅ <a href="../../app/Proofs.lean#L4010">App.unmount_keeps_node</a></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.dedupSorted_strict"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L151">Engine.dedupSorted_strict</a> · 21 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.lt_of_lt_le"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L38">Engine.Pos.lt_of_lt_le</a> · 19 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_lt_trans">Engine.Pos.cmp_lt_trans</a> ↪ · 18 below</li>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_dedupSorted"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L138">Engine.mem_dedupSorted</a> · 10 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.strict_of">Engine.strict_of</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.posLe_trans"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L129">Engine.posLe_trans</a> · 12 below</summary><ul>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.posLe_total"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L133">Engine.posLe_total</a> · 7 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.StrictB.le"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L54">Engine.StrictB.le</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_self">Engine.Pos.cmp_self</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.StrictB.gt"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L60">Engine.StrictB.gt</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.lt_swap">Engine.Pos.lt_swap</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.gt_swap"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L33">Engine.Pos.gt_swap</a> · 7 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.lt_swap"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L30">Engine.Pos.lt_swap</a> · 7 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_boundsOf"></a>▫️ <a href="../../engine/core/WindowIndex.lean#L188">Engine.mem_boundsOf</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_dedupSorted">Engine.mem_dedupSorted</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.countP_eq_nodup"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L62">Engine.countP_eq_nodup</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.nodup_nubB"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L52">Engine.nodup_nubB</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_nubB">Engine.mem_nubB</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_nubB"></a>▫️ <a href="../../engine/core/WindowLaws.lean#L43">Engine.mem_nubB</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Field.mono"></a>▫️ <a href="../../engine/core/Cost.lean#L369">Engine.Field.mono</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L357">Engine.Meter.add_diff</a></li>
</ul></details></li>
</ul>
