# Quality proofs › The engine

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › The engine**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1035) · 🌐 world: the node's code in a World (35) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (319) · 🧪 control: a negative control (24) · ▫️ lemma: not audited (2003)

<ul>
<li><details><summary><a id="law-Engine.same_ops_same_verdicts"></a>✅ <a href="../../engine/core/Termination.lean#L122">Engine.same_ops_same_verdicts</a> · 72 below</summary><ul>
<li>✅ <a href="#law-Engine.order_free">Engine.order_free</a> ↪ · 66 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.order_free"></a>✅ <a href="../../engine/core/Proofs.lean#L637">Engine.order_free</a> · 66 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.status_eq_of_ops"></a>▫️ <a href="../../engine/core/Proofs.lean#L496">Engine.status_eq_of_ops</a> · 10 below</summary><ul>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Engine.reach_drain"></a>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
<li><details><summary><a id="law-Engine.drain_settles"></a>✅ <a href="../../engine/core/Termination.lean#L112">Engine.drain_settles</a> · 70 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.status_iff_spec"></a>✅ <a href="../../engine/core/Proofs.lean#L484">Engine.status_iff_spec</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.undecided_spec"></a>▫️ <a href="../../engine/core/Proofs.lean#L454">Engine.undecided_spec</a> · 7 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.specAt_det">Engine.specAt_det</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.spec_extends"></a>📐 <a href="../../engine/core/SpecLemmas.lean#L138">Engine.spec_extends</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_extends"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L119">Engine.specAt_extends</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.inv_ingest"></a>✅ <a href="../../engine/core/Proofs.lean#L229">Engine.inv_ingest</a> · 8 below</summary><ul>
<li>📐 <a href="#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.inv_step"></a>✅ <a href="../../engine/core/Proofs.lean#L260">Engine.inv_step</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.spec_of_judge"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L169">Engine.spec_of_judge</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.common_depth"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L143">Engine.common_depth</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.specAt_le">Engine.specAt_le</a> ↪ · 5 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.decideS_nodup"></a>▫️ <a href="../../engine/core/Proofs.lean#L176">Engine.decideS_nodup</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.indexAllS_nodup"></a>▫️ <a href="../../engine/core/Proofs.lean#L120">Engine.indexAllS_nodup</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.ins_nodup">Engine.ins_nodup</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_waitOnS"></a>▫️ <a href="../../engine/core/Proofs.lean#L39">Engine.mem_waitOnS</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_stored">Engine.decideS_stored</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L30">Engine.waitOnS_idx</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L18">Engine.waitOnS_ops</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L34">Engine.waitOnS_stored</a></li>
</ul></details></li>
<li><a id="law-Engine.ingestS_known"></a>✅ <a href="../../engine/core/IdemLaws.lean#L23">Engine.ingestS_known</a></li>
<li><details><summary><a id="law-Engine.ingestS_twice"></a>✅ <a href="../../engine/core/IdemLaws.lean#L45">Engine.ingestS_twice</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/IdemLaws.lean#L27">Engine.ingestS_holds</a></li>
<li>✅ <a href="../../engine/core/IdemLaws.lean#L23">Engine.ingestS_known</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ingest_twice"></a>✅ <a href="../../engine/core/IdemLaws.lean#L50">Engine.ingest_twice</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Engine.ingestS_twice">Engine.ingestS_twice</a> ↪ · 2 below</li>
<li>✅ <a href="../../engine/core/Run.lean#L112">Engine.run_ingest</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.run_ingestEach"></a>✅ <a href="../../engine/core/IdemLaws.lean#L74">Engine.run_ingestEach</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Run.lean#L112">Engine.run_ingest</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ingestAll_again"></a>✅ <a href="../../engine/core/IdemLaws.lean#L83">Engine.ingestAll_again</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.ingestAll_mem"></a>▫️ <a href="../../engine/core/IdemLaws.lean#L64">Engine.ingestAll_mem</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.ingestAll_holds"></a>▫️ <a href="../../engine/core/IdemLaws.lean#L57">Engine.ingestAll_holds</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/IdemLaws.lean#L34">Engine.ingestS_keeps</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/IdemLaws.lean#L27">Engine.ingestS_holds</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/IdemLaws.lean#L23">Engine.ingestS_known</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_gone"></a>✅ <a href="../../engine/core/Purge.lean#L565">Engine.purge_gone</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_purgeS_idx"></a>▫️ <a href="../../engine/core/Purge.lean#L434">Engine.mem_purgeS_idx</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.purgeSet_closeUp"></a>▫️ <a href="../../engine/core/Purge.lean#L388">Engine.purgeSet_closeUp</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_shared"></a>✅ <a href="../../engine/core/Purge.lean#L578">Engine.purge_shared</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_settles"></a>✅ <a href="../../engine/core/Budget.lean#L196">Engine.purge_settles</a> · 106 below</summary><ul>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_bounded">Engine.drain_bounded</a> ↪ · 56 below</li>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.run_purge"></a>✅ <a href="../../engine/core/Purge.lean#L554">Engine.run_purge</a> · 19 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_walk">Engine.closeUp_walk</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.deleteAllS_eq"></a>▫️ <a href="../../engine/core/Purge.lean#L523">Engine.deleteAllS_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L501">Engine.filter_has_nil</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L498">Engine.not_has_cons</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.undecideAllS_eq"></a>▫️ <a href="../../engine/core/Purge.lean#L504">Engine.undecideAllS_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L501">Engine.filter_has_nil</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L498">Engine.not_has_cons</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L492">Engine.run_deleteAll</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L72">Engine.run_pushAll</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L452">Engine.run_unsettle</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L166">Engine.run_walkDeps</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.purge_named">Engine.purge_named</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Engine.purge_undecides"></a>✅ <a href="../../engine/core/Proofs.lean#L380">Engine.purge_undecides</a> · 23 below</summary><ul>
<li><details><summary><a id="law-Engine.closeUp_dependents"></a>▫️ <a href="../../engine/core/Proofs.lean#L360">Engine.closeUp_dependents</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_closed">Engine.closeUp_closed</a> ↪ · 11 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_sub">Engine.closeUp_sub</a> ↪ · 11 below</li>
<li>✅ <a href="#law-Engine.purge_shared">Engine.purge_shared</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.mem_purgeS_idx">Engine.mem_purgeS_idx</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.mem_purgeS_queue"></a>▫️ <a href="../../engine/core/Purge.lean#L428">Engine.mem_purgeS_queue</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purgeS_status_mem"></a>▫️ <a href="../../engine/core/Purge.lean#L403">Engine.purgeS_status_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L375">Engine.mem_rejudgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_inv"></a>✅ <a href="../../engine/core/Proofs.lean#L395">Engine.purge_inv</a> · 34 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_dependents">Engine.closeUp_dependents</a> ↪ · 12 below</li>
<li>📐 <a href="quality-proofs-sync.md#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.mem_purgeS_waits">Engine.mem_purgeS_waits</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.mem_purgeS_idx">Engine.mem_purgeS_idx</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.mem_purgeS_queue">Engine.mem_purgeS_queue</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.mem_purgeS_stored"></a>▫️ <a href="../../engine/core/Purge.lean#L413">Engine.mem_purgeS_stored</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.purgeS_status_mem">Engine.purgeS_status_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.purgeS_status_not"></a>▫️ <a href="../../engine/core/Purge.lean#L408">Engine.purgeS_status_not</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.purgeSet_closeUp">Engine.purgeSet_closeUp</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L375">Engine.mem_rejudgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_inv"></a>✅ <a href="../../engine/core/Proofs.lean#L522">Engine.reach_inv</a> · 56 below</summary><ul>
<li>✅ <a href="#law-Engine.purge_inv">Engine.purge_inv</a> ↪ · 34 below</li>
<li>✅ <a href="#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
<li>✅ <a href="#law-Engine.inv_ingest">Engine.inv_ingest</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L221">Engine.inv_empty</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_purgeSet"></a>✅ <a href="../../engine/core/Proofs.lean#L366">Engine.mem_purgeSet</a> · 17 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_dependents">Engine.closeUp_dependents</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.closeUp_sound"></a>▫️ <a href="../../engine/core/Purge.lean#L312">Engine.closeUp_sound</a> · 11 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_walk">Engine.closeUp_walk</a> ↪ · 10 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_sub">Engine.closeUp_sub</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_ops"></a>✅ <a href="../../engine/core/Proofs.lean#L625">Engine.reach_ops</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.reach_stored"></a>▫️ <a href="../../engine/core/Proofs.lean#L573">Engine.reach_stored</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_held"></a>▫️ <a href="../../engine/core/Proofs.lean#L598">Engine.reach_held</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sum_left"></a>✅ <a href="../../engine/core/Families.lean#L80">Engine.sum_left</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Families.lean#L74">Engine.lefts_map</a></li>
</ul></details></li>
<li><a id="law-Engine.sum_scope_left"></a>✅ <a href="../../engine/core/Families.lean#L85">Engine.sum_scope_left</a></li>
<li><a id="law-Engine.Codec.decode_encode"></a>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li><details><summary><a id="law-Engine.Op.decode_bytes"></a>✅ <a href="../../engine/core/Core.lean#L96">Engine.Op.decode_bytes</a> · 34 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
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
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sum_project"></a>✅ <a href="../../engine/core/Project.lean#L427">Engine.sum_project</a> · 40 below</summary><ul>
<li>✅ <a href="#law-Engine.view_proj">Engine.view_proj</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Engine.proj_inv"></a>✅ <a href="../../engine/core/Project.lean#L220">Engine.proj_inv</a> · 32 below</summary><ul>
<li><details><summary><a id="law-Engine.proj_status"></a>✅ <a href="../../engine/core/Project.lean#L210">Engine.proj_status</a> · 25 below</summary><ul>
<li>✅ <a href="#law-Engine.spec_sum_left">Engine.spec_sum_left</a> ↪ · 19 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li><details><summary><a id="law-Engine.specVerdict_eq_some"></a>📐 <a href="../../engine/core/Project.lean#L71">Engine.specVerdict_eq_some</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.specVerdict_eq_some">Engine.specVerdict_eq_some</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.spec_of_judge">Engine.spec_of_judge</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.leftOps_isSome"></a>📐 <a href="../../engine/core/Project.lean#L56">Engine.leftOps_isSome</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L215">Engine.mem_proj_idx</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L206">Engine.proj_ops</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.spec_sum_left">Engine.spec_sum_left</a> ↪ · 19 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sum_project_node"></a>✅ <a href="../../app/connection/Family.lean#L622">Connection.sum_project_node</a> · 80 below</summary><ul>
<li>✅ <a href="#law-Engine.sum_project">Engine.sum_project</a> ↪ · 40 below</li>
<li><details><summary><a id="law-Engine.leftKey_rels"></a>✅ <a href="../../engine/core/Project.lean#L337">Engine.leftKey_rels</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Engine.leftKey_rel"></a>✅ <a href="../../engine/core/Project.lean#L322">Engine.leftKey_rel</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.Rel.key_names"></a>✅ <a href="../../engine/core/Project.lean#L311">Engine.Rel.key_names</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Codec.encode_inj">Engine.Codec.encode_inj</a> ↪ · 1 below</li>
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
<li>✅ <a href="../../engine/core/Project.lean#L298">Engine.leftKey_of</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1434">Community.rels_short</a></li>
<li>✅ <a href="../../app/connection/Family.lean#L611">Connection.rels_apart</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L289">Engine.View.Reads.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.spec_sum_left"></a>✅ <a href="../../engine/core/Project.lean#L197">Engine.spec_sum_left</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_left"></a>✅ <a href="../../engine/core/Project.lean#L182">Engine.specAt_left</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.specAt_valid_inv"></a>📐 <a href="../../engine/core/Project.lean#L105">Engine.specAt_valid_inv</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L192">Engine.allValid_forall2</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L131">Engine.All2.to_map</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.specAt_inl"></a>✅ <a href="../../engine/core/Project.lean#L158">Engine.specAt_inl</a> · 14 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>📐 <a href="#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L126">Engine.All2.of_map</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L138">Engine.lefts_some</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.view_proj"></a>✅ <a href="../../engine/core/Project.lean#L410">Engine.view_proj</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.eval_proj"></a>📐 <a href="../../engine/core/Project.lean#L387">Engine.eval_proj</a> · 32 below</summary><ul>
<li><details><summary><a id="law-Engine.matching_proj"></a>📐 <a href="../../engine/core/Project.lean#L366">Engine.matching_proj</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.proj_status">Engine.proj_status</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Engine.sortPos_map"></a>📐 <a href="../../engine/core/Project.lean#L359">Engine.sortPos_map</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/core/Project.lean#L350">Engine.insertBy_map</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L128">Engine.filterMap_congr'</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L215">Engine.mem_proj_idx</a></li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="../../engine/core/Project.lean#L404">Engine.filterMap_inlRow</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.connect_iff_node"></a>✅ <a href="../../app/connection/Proofs.lean#L600">Connection.connect_iff_node</a> · 115 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_allowPeer">Community.reads_allowPeer</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.members_iff_node"></a>📐 <a href="../../app/connection/Proofs.lean#L444">Connection.members_iff_node</a> · 116 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>📐 <a href="security-proofs-confidentiality.md#law-Community.members_iff">Community.members_iff</a> ↪ · 69 below</li>
<li><details><summary><a id="law-Community.reads_members"></a>📐 <a href="../../app/connection/Family.lean#L594">Community.reads_members</a> · 5 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_live">Community.reads_live</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.recipients_iff_node"></a>📐 <a href="../../app/connection/Proofs.lean#L452">Connection.recipients_iff_node</a> · 116 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>📐 <a href="security-proofs-confidentiality.md#law-Community.recipients_iff">Community.recipients_iff</a> ↪ · 69 below</li>
<li><details><summary><a id="law-Community.reads_recipients"></a>📐 <a href="../../app/connection/Family.lean#L598">Community.reads_recipients</a> · 5 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_live">Community.reads_live</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.node_settles"></a>✅ <a href="../../app/connection/Proofs.lean#L461">Connection.node_settles</a> · 66 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.current_newest"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L53">Settings.Appearance.current_newest</a> · 64 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.query_right"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L42">Settings.Appearance.query_right</a> · 37 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.not_relKey"></a>▫️ <a href="../../app/settings/appearance/Proofs.lean#L29">Settings.Appearance.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
<li>✅ <a href="../../engine/core/Left.lean#L129">Engine.rightKey_of</a></li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L25">Settings.Appearance.apart_community</a></li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L26">Settings.Appearance.apart_connection</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.top_right"></a>✅ <a href="../../engine/core/Left.lean#L142">Engine.top_right</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.top_max"></a>✅ <a href="../../engine/core/Order.lean#L173">Engine.top_max</a> · 21 below</summary><ul>
<li><details><summary><a id="law-Engine.sortPos_sorted"></a>📐 <a href="../../engine/core/Order.lean#L153">Engine.sortPos_sorted</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.insertBy_sorted"></a>▫️ <a href="../../engine/core/Order.lean#L132">Engine.insertBy_sorted</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/core/Decl.lean#L124">Engine.perm_insertBy</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sorted_last"></a>▫️ <a href="../../engine/core/Order.lean#L157">Engine.sorted_last</a> · 10 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.choose_valid"></a>✅ <a href="../../app/settings/appearance/Commands.lean#L18">Settings.Appearance.choose_valid</a> · 26 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../app/settings/appearance/Op.lean#L32">Settings.Appearance.ofCode_code</a></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.choose_local"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L19">Settings.Appearance.choose_local</a> · 24 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Quiet.node_left"></a>✅ <a href="../../app/Family.lean#L52">Quiet.node_left</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.left_list"></a>✅ <a href="../../engine/core/Left.lean#L94">Engine.left_list</a> · 34 below</summary><ul>
<li>📐 <a href="#law-Engine.eval_proj">Engine.eval_proj</a> ↪ · 32 below</li>
<li>📐 <a href="../../engine/core/Project.lean#L404">Engine.filterMap_inlRow</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.request_valid"></a>✅ <a href="../../app/community/member/invite/request/Proofs.lean#L48">Community.request_valid</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.approve_valid"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L65">Community.approve_valid</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.admit_admits"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L83">Community.admit_admits</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.connect_admitted"></a>✅ <a href="../../app/community/Proofs.lean#L845">Community.connect_admitted</a> · 85 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="#law-Community.admit_admits">Community.admit_admits</a> ↪ · 49 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.removeMember_valid"></a>✅ <a href="../../app/community/Proofs.lean#L453">Community.removeMember_valid</a> · 85 below</summary><ul>
<li><details><summary><a id="law-Community.row_filed"></a>▫️ <a href="../../app/community/Family.lean#L1471">Community.row_filed</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1405">Community.matching_also_nil</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1409">Community.mem_eval_matching</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admin_removal_stands">Community.admin_removal_stands</a> ↪ · 49 below</li>
<li><details><summary><a id="law-Community.root_of_admission"></a>✅ <a href="../../app/community/Proofs.lean#L151">Community.root_of_admission</a> · 46 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.check_admission">Community.check_admission</a> ↪ · 24 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1185">Community.all2_cons2</a></li>
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
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1466">Community.admission_byUser_args</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1484">Community.byDevice_args</a></li>
<li>▫️ <a href="../../app/community/member/admin/Proofs.lean#L34">Community.isAdmin_sound</a></li>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.Pos.cmp_trans"></a>▫️ <a href="../../engine/core/Query.lean#L214">Engine.Pos.cmp_trans</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_lt_trans"></a>▫️ <a href="../../engine/core/Query.lean#L201">Engine.bcmp_lt_trans</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_eq"></a>▫️ <a href="../../engine/core/Query.lean#L193">Engine.bcmp_eq</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_eq_lexCmp"></a>▫️ <a href="../../engine/core/Query.lean#L136">Engine.bcmp_eq_lexCmp</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmpFrom_eq"></a>▫️ <a href="../../engine/core/Query.lean#L117">Engine.bcmpFrom_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Query.lean#L113">Engine.drop_data_cons</a></li>
<li>▫️ <a href="../../engine/core/Query.lean#L110">Engine.drop_data_nil</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Query.lean#L153">Engine.lexCmp_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_swap"></a>▫️ <a href="../../engine/core/Query.lean#L190">Engine.bcmp_swap</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L140">Engine.lexCmp_swap</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_trans"></a>▫️ <a href="../../engine/core/Query.lean#L197">Engine.bcmp_trans</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L169">Engine.lexCmp_trans</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.bcmp_trans">Engine.bcmp_trans</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.cmp_swap"></a>✅ <a href="../../engine/core/Query.lean#L211">Engine.Pos.cmp_swap</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_swap">Engine.bcmp_swap</a> ↪ · 5 below</li>
</ul></details></li>
</ul>
