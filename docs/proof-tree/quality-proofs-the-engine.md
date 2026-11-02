# Quality proofs › The engine

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › The engine**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1377) · 🌐 world: the node's code in a World (69) · 🪜 step: a step of a wired law (57) · 📐 model: over a model (69) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2175)

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
<li><details><summary><a id="law-Engine.spec_extends"></a>✅ <a href="../../engine/core/SpecLemmas.lean#L138">Engine.spec_extends</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_extends"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L119">Engine.specAt_extends</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.inv_ingest"></a>✅ <a href="../../engine/core/Proofs.lean#L229">Engine.inv_ingest</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
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
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
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
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
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
<li><details><summary><a id="law-Engine.Op.decode_bytes"></a>✅ <a href="../../engine/core/Core.lean#L97">Engine.Op.decode_bytes</a> · 34 below</summary><ul>
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
<li><details><summary><a id="law-Engine.specVerdict_eq_some"></a>🪜 <a href="../../engine/core/Project.lean#L71">Engine.specVerdict_eq_some</a> · 8 below · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +13</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
</ul></details></li>
<li>🪜 <a href="#law-Engine.specVerdict_eq_some">Engine.specVerdict_eq_some</a> ↪ · 8 below · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +13</li>
<li>▫️ <a href="#law-Engine.spec_of_judge">Engine.spec_of_judge</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.leftOps_isSome"></a>🪜 <a href="../../engine/core/Project.lean#L56">Engine.leftOps_isSome</a> · 1 below · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +9</summary><ul>
<li>🪜 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +16</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>🪜 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +16</li>
<li>🪜 <a href="../../engine/core/Project.lean#L215">Engine.mem_proj_idx</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +11</li>
<li>✅ <a href="../../engine/core/Project.lean#L206">Engine.proj_ops</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.spec_sum_left">Engine.spec_sum_left</a> ↪ · 19 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>🪜 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +16</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sum_project_node"></a>✅ <a href="../../app/connection/Family.lean#L702">Connection.sum_project_node</a> · 80 below</summary><ul>
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
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L298">Engine.leftKey_of</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1657">Community.rels_short</a></li>
<li>✅ <a href="../../app/connection/Family.lean#L691">Connection.rels_apart</a></li>
<li>🪜 <a href="../../engine/core/Project.lean#L289">Engine.View.Reads.mono</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +6</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.spec_sum_left"></a>✅ <a href="../../engine/core/Project.lean#L197">Engine.spec_sum_left</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_left"></a>✅ <a href="../../engine/core/Project.lean#L182">Engine.specAt_left</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.specAt_valid_inv"></a>✅ <a href="../../engine/core/Project.lean#L105">Engine.specAt_valid_inv</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L192">Engine.allValid_forall2</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>🪜 <a href="../../engine/core/Project.lean#L131">Engine.All2.to_map</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +15</li>
<li>🪜 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +16</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.specAt_inl"></a>✅ <a href="../../engine/core/Project.lean#L158">Engine.specAt_inl</a> · 14 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>✅ <a href="#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>🪜 <a href="../../engine/core/Project.lean#L126">Engine.All2.of_map</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +15</li>
<li>🪜 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +16</li>
<li>✅ <a href="../../engine/core/Project.lean#L138">Engine.lefts_some</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.view_proj"></a>✅ <a href="../../engine/core/Project.lean#L410">Engine.view_proj</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.eval_proj"></a>🪜 <a href="../../engine/core/Project.lean#L387">Engine.eval_proj</a> · 32 below · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +9</summary><ul>
<li><details><summary><a id="law-Engine.matching_proj"></a>🪜 <a href="../../engine/core/Project.lean#L366">Engine.matching_proj</a> · 31 below · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +9</summary><ul>
<li>✅ <a href="#law-Engine.proj_status">Engine.proj_status</a> ↪ · 25 below</li>
<li>✅ <a href="#law-Engine.sortPos_map">Engine.sortPos_map</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L128">Engine.filterMap_congr'</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>🪜 <a href="../../engine/core/Project.lean#L215">Engine.mem_proj_idx</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +11</li>
</ul></details></li>
</ul></details></li>
<li>🪜 <a href="../../engine/core/Project.lean#L404">Engine.filterMap_inlRow</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +9</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.connect_iff_node"></a>✅ <a href="../../app/connection/Proofs.lean#L634">Connection.connect_iff_node</a> · 167 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_allowPeer">Community.reads_allowPeer</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.node_settles"></a>✅ <a href="../../app/connection/Proofs.lean#L494">Connection.node_settles</a> · 66 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.trace_good"></a>🌐 <a href="../../app/Proofs.lean#L2863">Connection.Execution.trace_good</a> · 222 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.empty_trace_store"></a>📐 <a href="../../app/Proofs.lean#L2812">Connection.Execution.empty_trace_store</a> · 178 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.world_trace_moves"></a>📐 <a href="../../app/Proofs.lean#L2803">Connection.Execution.world_trace_moves</a> · 139 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.world_step_moves"></a>📐 <a href="../../app/Proofs.lean#L2767">Connection.Execution.world_step_moves</a> · 138 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.production_step_moves"></a>📐 <a href="../../app/Proofs.lean#L2730">Connection.Execution.production_step_moves</a> · 136 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.production_readOnly">Connection.Execution.NodeTape.production_readOnly</a> ↪ · 85 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.step_goes">Connection.Execution.NodeTape.step_goes</a> ↪ · 81 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.production_readOnly">Connection.Execution.NodeTape.production_readOnly</a> ↪ · 85 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onClose_goes"></a>▫️ <a href="../../app/Proofs.lean#L2657">Connection.Execution.NodeTape.onClose_goes</a> · 44 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2754">Connection.Execution.world_run_moves</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Moves.store_settled"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L145">Engine.Sync.Moves.store_settled</a> · 66 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.turn_settles_reachable"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L86">Engine.Sync.turn_settles_reachable</a> · 59 below</summary><ul>
<li><details><summary><a id="law-Engine.drain_history_budget"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L61">Engine.drain_history_budget</a> · 54 below</summary><ul>
<li>✅ <a href="#law-Engine.step_history_budget">Engine.step_history_budget</a> ↪ · 53 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.budget_same_ops"></a>🪜 <a href="../../engine/sync/ClosureStore.lean#L154">Engine.Sync.budget_same_ops</a> · 32 below · a step of App.stash_use, App.withNav_cache, Data.draftIn_newest +10</summary><ul>
<li>🪜 <a href="#law-Engine.Sync.dedup_nodup">Engine.Sync.dedup_nodup</a> ↪ · 31 below · a step of App.stash_use, App.withNav_cache, Data.draftIn_newest +10</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L170">Engine.Sync.ingest_many_reachable</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L434">Engine.Sync.turn_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.purge_settles_reachable"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L107">Engine.Sync.purge_settles_reachable</a> · 58 below</summary><ul>
<li>✅ <a href="#law-Engine.drain_history_budget">Engine.drain_history_budget</a> ↪ · 54 below</li>
<li>🪜 <a href="#law-Engine.Sync.budget_same_ops">Engine.Sync.budget_same_ops</a> ↪ · 32 below · a step of App.stash_use, App.withNav_cache, Data.draftIn_newest +10</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L484">Engine.Sync.purge_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Moves.store_reachable"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L136">Engine.Sync.Moves.store_reachable</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.turn_reachable"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L178">Engine.Sync.turn_reachable</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L170">Engine.Sync.ingest_many_reachable</a></li>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.purge_reachable"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L98">Engine.Sync.purge_reachable</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Proofs.lean#L529">Engine.reach_drain</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.Moves.store_reachable">Engine.Sync.Moves.store_reachable</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L167">Engine.Sync.held_empty_reachable</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.Run.good"></a>🌐 <a href="../../app/Proofs.lean#L2922">Connection.Execution.Run.good</a> · 224 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 222 below</li>
<li>🌐 <a href="../../app/Proofs.lean#L2910">Connection.Execution.Run.state_trace</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.admitted_trace"></a>🌐 <a href="../../app/Proofs.lean#L2895">Connection.Execution.admitted_trace</a> · 268 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 222 below</li>
<li><details><summary><a id="law-Connection.admitted_node"></a>✅ <a href="../../app/Proofs.lean#L1095">Connection.admitted_node</a> · 81 below</summary><ul>
<li>✅ <a href="#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.current_newest"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L72">Settings.Appearance.current_newest</a> · 67 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.query_only"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L54">Settings.Appearance.query_only</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.query_right"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L45">Settings.Appearance.query_right</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.not_relKey"></a>▫️ <a href="../../app/settings/appearance/Proofs.lean#L30">Settings.Appearance.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.key_ne_opKey"></a>▫️ <a href="../../app/settings/appearance/Proofs.lean#L41">Settings.Appearance.key_ne_opKey</a> · 30 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Left.lean#L129">Engine.rightKey_of</a></li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L25">Settings.Appearance.apart_community</a></li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L26">Settings.Appearance.apart_connection</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Settings.Appearance.not_relKey">Settings.Appearance.not_relKey</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Settings.Appearance.key_ne_opKey">Settings.Appearance.key_ne_opKey</a> ↪ · 30 below</li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L27">Settings.Appearance.apart_nav</a></li>
</ul></details></li>
<li>✅ <a href="#law-Settings.Appearance.query_right">Settings.Appearance.query_right</a> ↪ · 38 below</li>
<li><details><summary><a id="law-Engine.top_right"></a>✅ <a href="../../engine/core/Left.lean#L142">Engine.top_right</a> · 25 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.top_max">Engine.top_max</a> ↪ · 21 below</li>
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
<li><details><summary><a id="law-Quiet.node_left"></a>✅ <a href="../../app/Family.lean#L105">Quiet.node_left</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.left_list"></a>✅ <a href="../../engine/core/Left.lean#L94">Engine.left_list</a> · 34 below</summary><ul>
<li>🪜 <a href="#law-Engine.eval_proj">Engine.eval_proj</a> ↪ · 32 below · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +9</li>
<li>🪜 <a href="../../engine/core/Project.lean#L404">Engine.filterMap_inlRow</a> · a step of Connection.admitted_node, Connection.community_inv, Connection.connect_iff_node +9</li>
</ul></details></li>
<li><details><summary><a id="law-App.withNav_cache"></a>✅ <a href="../../app/nav/Proofs.lean#L124">App.withNav_cache</a> · 172 below</summary><ul>
<li>✅ <a href="#law-Data.placeIn_newest">Data.placeIn_newest</a> ↪ · 170 below</li>
<li>✅ <a href="../../app/Screen.lean#L2150">App.page_round</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.placeIn_newest"></a>✅ <a href="../../app/nav/Proofs.lean#L67">Data.placeIn_newest</a> · 170 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOps_valid"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L62">Engine.Sync.ofOps_valid</a> · 116 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOps_rest"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L44">Engine.Sync.ofOps_rest</a> · 63 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.turn_settles"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L188">Engine.Sync.turn_settles</a> · 61 below</summary><ul>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_bounded">Engine.drain_bounded</a> ↪ · 56 below</li>
<li>🪜 <a href="#law-Engine.Sync.budget_same_ops">Engine.Sync.budget_same_ops</a> ↪ · 32 below · a step of App.stash_use, App.withNav_cache, Data.draftIn_newest +10</li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L170">Engine.Sync.ingest_many_reachable</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L434">Engine.Sync.turn_apply</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L167">Engine.Sync.held_empty_reachable</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ofOps_inv"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L49">Engine.Sync.ofOps_inv</a> · 62 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li><details><summary><a id="law-Engine.Sync.ofOps_reach"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L36">Engine.Sync.ofOps_reach</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.turn_reachable">Engine.Sync.turn_reachable</a> ↪ · 2 below</li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L167">Engine.Sync.held_empty_reachable</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ofOps_ops"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L54">Engine.Sync.ofOps_ops</a> · 18 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_reach">Engine.Sync.ofOps_reach</a> ↪ · 4 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ofOps_from"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L71">Engine.Sync.ofOps_from</a> · 70 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 62 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_ops">Engine.Sync.ofOps_ops</a> ↪ · 18 below</li>
<li>✅ <a href="#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 62 below</li>
<li><details><summary><a id="law-Nav.query_only"></a>✅ <a href="../../app/nav/Proofs.lean#L39">Nav.query_only</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Nav.not_relKey"></a>▫️ <a href="../../app/nav/Proofs.lean#L22">Nav.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Nav.key_ne_opKey"></a>▫️ <a href="../../app/nav/Proofs.lean#L33">Nav.key_ne_opKey</a> · 30 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Left.lean#L129">Engine.rightKey_of</a></li>
<li>▫️ <a href="../../app/nav/Proofs.lean#L18">Nav.apart_community</a></li>
<li>▫️ <a href="../../app/nav/Proofs.lean#L19">Nav.apart_connection</a></li>
<li>▫️ <a href="../../app/nav/Proofs.lean#L20">Nav.apart_settings</a></li>
</ul></details></li>
<li><details><summary><a id="law-Nav.place_valid"></a>✅ <a href="../../app/nav/Commands.lean#L16">Nav.place_valid</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.top_right">Engine.top_right</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Quiet.node_nav"></a>✅ <a href="../../app/Family.lean#L64">Quiet.node_nav</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Family.lean#L48">Quiet.rights_map</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Ephemeral.lean#L29">Engine.Sync.run_eval</a></li>
<li>✅ <a href="../../app/Family.lean#L83">Quiet.node_nav_kind</a></li>
</ul></details></li>
<li><a id="law-Quiet.node_nav_ephemeral"></a>✅ <a href="../../app/Family.lean#L76">Quiet.node_nav_ephemeral</a></li>
<li><a id="law-Engine.intake_durable"></a>✅ <a href="../../engine/core/Sync.lean#L114">Engine.intake_durable</a></li>
<li><details><summary><a id="law-Engine.stored_durable"></a>✅ <a href="../../engine/core/Sync.lean#L204">Engine.stored_durable</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.stepS_ops-">Engine.stepS_ops'</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.foldl_ingest_ops">Engine.foldl_ingest_ops</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L114">Engine.intake_durable</a></li>
</ul></details></li>
<li><details><summary><a id="law-App.stash_use"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L257">App.stash_use</a> · 180 below</summary><ul>
<li>✅ <a href="#law-Data.draftIn_newest">Data.draftIn_newest</a> ↪ · 179 below</li>
</ul></details></li>
<li><details><summary><a id="law-Data.draftIn_newest"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L135">Data.draftIn_newest</a> · 179 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ofOps_valid">Engine.Sync.ofOps_valid</a> ↪ · 116 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_from">Engine.Sync.ofOps_from</a> ↪ · 70 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 62 below</li>
<li><details><summary><a id="law-Community.Draft.query_only"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L67">Community.Draft.query_only</a> · 42 below</summary><ul>
<li><details><summary><a id="law-Community.Draft.key_draft"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L28">Community.Draft.key_draft</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Engine.Rel.key_eq_iff"></a>▫️ <a href="../../engine/core/Decl.lean#L65">Engine.Rel.key_eq_iff</a> · 30 below</summary><ul>
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
<li><details><summary><a id="law-Community.Draft.rel_draft"></a>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L21">Community.Draft.rel_draft</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L19">Community.Draft.draft_rels</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.not_relKey"></a>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L51">Community.Draft.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.key_ne_opKey"></a>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L63">Community.Draft.key_ne_opKey</a> · 30 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L47">Community.Draft.apart_connection</a></li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L49">Community.Draft.apart_nav</a></li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L48">Community.Draft.apart_settings</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.node_draft"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L89">Community.Draft.node_draft</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L81">Community.Draft.check_draft</a></li>
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
<li>✅ <a href="#law-Community.Draft.write_valid">Community.Draft.write_valid</a> ↪ · 41 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Engine.top_max">Engine.top_max</a> ↪ · 21 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>✅ <a href="#law-Quiet.node_left">Quiet.node_left</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Community.Draft.isFor_of"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L121">Community.Draft.isFor_of</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L19">Community.Draft.draft_rels</a></li>
<li>✅ <a href="../../engine/sync/Ephemeral.lean#L29">Engine.Sync.run_eval</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.draftIn_empty"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L219">Data.draftIn_empty</a> · 136 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ofOps_from">Engine.Sync.ofOps_from</a> ↪ · 70 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 62 below</li>
<li>✅ <a href="#law-Community.Draft.query_only">Community.Draft.query_only</a> ↪ · 42 below</li>
<li>✅ <a href="#law-Community.Draft.node_draft">Community.Draft.node_draft</a> ↪ · 41 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>✅ <a href="#law-Community.Draft.isFor_of">Community.Draft.isFor_of</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L202">Data.mem_eval_matching</a></li>
<li>✅ <a href="../../engine/sync/Ephemeral.lean#L29">Engine.Sync.run_eval</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.write_ephemeral"></a>✅ <a href="../../app/community/channel/message/draft/Commands.lean#L34">Community.Draft.write_ephemeral</a> · 42 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.Draft.write_valid"></a>✅ <a href="../../app/community/channel/message/draft/Commands.lean#L29">Community.Draft.write_valid</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
</ul></details></li>
<li><details><summary><a id="law-Engine.perm_sortPos"></a>✅ <a href="../../engine/core/Decl.lean#L133">Engine.perm_sortPos</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Decl.lean#L124">Engine.perm_insertBy</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sortPos_sorted"></a>✅ <a href="../../engine/core/Order.lean#L153">Engine.sortPos_sorted</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.insertBy_sorted"></a>▫️ <a href="../../engine/core/Order.lean#L132">Engine.insertBy_sorted</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_trans"></a>▫️ <a href="../../engine/core/Query.lean#L214">Engine.Pos.cmp_trans</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_lt_trans"></a>▫️ <a href="../../engine/core/Query.lean#L201">Engine.bcmp_lt_trans</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_eq"></a>▫️ <a href="../../engine/core/Query.lean#L193">Engine.bcmp_eq</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L153">Engine.lexCmp_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_swap"></a>▫️ <a href="../../engine/core/Query.lean#L190">Engine.bcmp_swap</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L140">Engine.lexCmp_swap</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_trans"></a>▫️ <a href="../../engine/core/Query.lean#L197">Engine.bcmp_trans</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L169">Engine.lexCmp_trans</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.bcmp_trans">Engine.bcmp_trans</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.cmp_swap"></a>✅ <a href="../../engine/core/Query.lean#L211">Engine.Pos.cmp_swap</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_swap">Engine.bcmp_swap</a> ↪ · 5 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Decl.lean#L124">Engine.perm_insertBy</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sortPos_eq_fast"></a>✅ <a href="../../engine/core/Query.lean#L279">Engine.sortPos_eq_fast</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.posLE_trans"></a>▫️ <a href="../../engine/core/Query.lean#L253">Engine.posLE_trans</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.posLE_total"></a>▫️ <a href="../../engine/core/Query.lean#L256">Engine.posLE_total</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.insertBy_split"></a>▫️ <a href="../../engine/core/Query.lean#L260">Engine.insertBy_split</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sortPos_map"></a>✅ <a href="../../engine/core/Project.lean#L359">Engine.sortPos_map</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Project.lean#L350">Engine.insertBy_map</a></li>
</ul></details></li>
<li><a id="law-Engine.insertBy_map"></a>✅ <a href="../../engine/core/Project.lean#L350">Engine.insertBy_map</a></li>
<li><details><summary><a id="law-Engine.foldr_insertBy"></a>✅ <a href="../../engine/core/Union.lean#L113">Engine.foldr_insertBy</a> · 18 below</summary><ul>
<li>✅ <a href="#law-Engine.insertBy_merge">Engine.insertBy_merge</a> ↪ · 17 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.insertBy_merge"></a>✅ <a href="../../engine/core/Union.lean#L76">Engine.insertBy_merge</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_gt_of_le"></a>✅ <a href="../../engine/core/Query.lean#L242">Engine.Pos.cmp_gt_of_le</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_lt_le_trans"></a>✅ <a href="../../engine/core/Query.lean#L231">Engine.Pos.cmp_lt_le_trans</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Pos.cmp_eq"></a>✅ <a href="../../engine/core/Query.lean#L227">Engine.Pos.cmp_eq</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mergeRuns_eq_sortPos"></a>✅ <a href="../../engine/core/Union.lean#L121">Engine.mergeRuns_eq_sortPos</a> · 19 below</summary><ul>
<li>✅ <a href="#law-Engine.foldr_insertBy">Engine.foldr_insertBy</a> ↪ · 18 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.union_rows"></a>✅ <a href="../../engine/core/Union.lean#L167">Engine.union_rows</a> · 20 below</summary><ul>
<li>✅ <a href="#law-Engine.mergeRuns_eq_sortPos">Engine.mergeRuns_eq_sortPos</a> ↪ · 19 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.request_valid"></a>✅ <a href="../../app/community/member/invite/request/Proofs.lean#L49">Community.request_valid</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.approve_valid"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L192">Community.approve_valid</a> · 50 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L7">Community.approvals_map</a></li>
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
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admit_admits">Community.admit_admits</a> ↪ · 49 below</li>
<li><details><summary><a id="law-Community.connect_admitted"></a>✅ <a href="../../app/community/Proofs.lean#L1747">Community.connect_admitted</a> · 123 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
<li><details><summary><a id="law-Community.approval_request"></a>▫️ <a href="../../app/community/Proofs.lean#L1735">Community.approval_request</a> · 57 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.approval_signed">Community.approval_signed</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admit_admits">Community.admit_admits</a> ↪ · 49 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.removeMember_valid"></a>✅ <a href="../../app/community/Proofs.lean#L751">Community.removeMember_valid</a> · 89 below</summary><ul>
<li><details><summary><a id="law-Community.headsOf_valid"></a>▫️ <a href="../../app/community/Proofs.lean#L714">Community.headsOf_valid</a> · 58 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.row_filed">Community.row_filed</a> ↪ · 55 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.row_filed">Community.row_filed</a> ↪ · 55 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admin_removal_stands">Community.admin_removal_stands</a> ↪ · 50 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Community.root_of_admission">Community.root_of_admission</a> ↪ · 46 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1689">Community.admission_byUser_args</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1707">Community.byDevice_args</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L739">Community.cut_of_heads</a></li>
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
<li><details><summary><a id="law-Connection.Execution.NodeTape.production_readOnly"></a>▫️ <a href="../../app/Proofs.lean#L2537">Connection.Execution.NodeTape.production_readOnly</a> · 85 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.hooks_reads">Connection.hooks_reads</a> ↪ · 83 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2187">Connection.Execution.fresh_reads</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.step_goes"></a>▫️ <a href="../../app/Proofs.lean#L2719">Connection.Execution.NodeTape.step_goes</a> · 81 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onTick_goes"></a>▫️ <a href="../../app/Proofs.lean#L2705">Connection.Execution.NodeTape.onTick_goes</a> · 73 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.apply_goes"></a>▫️ <a href="../../app/Proofs.lean#L2659">Connection.Execution.NodeTape.apply_goes</a> · 26 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.store_goes"></a>▫️ <a href="../../app/Proofs.lean#L2632">Connection.Execution.NodeTape.store_goes</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.fanout_goes"></a>▫️ <a href="../../app/Proofs.lean#L2628">Connection.Execution.NodeTape.fanout_goes</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.recordGiven_goes">Connection.Execution.NodeTape.recordGiven_goes</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.filedGive_reads">Connection.Execution.NodeTape.filedGive_reads</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.put_goes"></a>▫️ <a href="../../app/Proofs.lean#L2620">Connection.Execution.NodeTape.put_goes</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.write_goes">Connection.Execution.NodeTape.write_goes</a> ↪ · 10 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.recordGiven_goes">Connection.Execution.NodeTape.recordGiven_goes</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.store_goes">Connection.Execution.NodeTape.store_goes</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.serve_afterActs_goes"></a>▫️ <a href="../../app/Proofs.lean#L2690">Connection.Execution.NodeTape.serve_afterActs_goes</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.serve_goes"></a>▫️ <a href="../../app/Proofs.lean#L2663">Connection.Execution.NodeTape.serve_goes</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.serveOwed_reads"></a>▫️ <a href="../../app/Proofs.lean#L2611">Connection.Execution.NodeTape.serveOwed_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.read_program">Connection.Execution.NodeTape.read_program</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2548">Connection.Execution.NodeTape.ReadOnly.afterActs</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sweep_afterActs_goes"></a>▫️ <a href="../../app/Proofs.lean#L2686">Connection.Execution.NodeTape.sweep_afterActs_goes</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sweep_goes"></a>▫️ <a href="../../app/Proofs.lean#L2667">Connection.Execution.NodeTape.sweep_goes</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sweep_reads"></a>▫️ <a href="../../app/Proofs.lean#L2553">Connection.Execution.NodeTape.sweep_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2548">Connection.Execution.NodeTape.ReadOnly.afterActs</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.sweep_goes">Connection.Execution.NodeTape.sweep_goes</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.tickGive_reads"></a>▫️ <a href="../../app/Proofs.lean#L2604">Connection.Execution.NodeTape.tickGive_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.give_reads"></a>▫️ <a href="../../app/Proofs.lean#L2594">Connection.Execution.NodeTape.give_reads</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.closure_reads"></a>▫️ <a href="../../app/Proofs.lean#L2573">Connection.Execution.NodeTape.closure_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L103">Engine.Sync.closureOps_cons</a></li>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L116">Engine.Sync.closureOps_zero</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onFrame_goes"></a>▫️ <a href="../../app/Proofs.lean#L2700">Connection.Execution.NodeTape.onFrame_goes</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onSealed_goes"></a>▫️ <a href="../../app/Proofs.lean#L2694">Connection.Execution.NodeTape.onSealed_goes</a> · 70 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.apply_goes">Connection.Execution.NodeTape.apply_goes</a> ↪ · 26 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.serve_goes">Connection.Execution.NodeTape.serve_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.recv_reads"></a>▫️ <a href="../../app/Proofs.lean#L2608">Connection.Execution.NodeTape.recv_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onHold_reads"></a>▫️ <a href="../../app/Proofs.lean#L2568">Connection.Execution.NodeTape.onHold_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.holdsIn_reads">Connection.Execution.NodeTape.holdsIn_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.refresh_reads">Connection.Execution.NodeTape.refresh_reads</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
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
<li>▫️ <a href="#law-Connection.Execution.NodeTape.write_goes">Connection.Execution.NodeTape.write_goes</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.onWrite_goes"></a>▫️ <a href="../../app/Proofs.lean#L2714">Connection.Execution.NodeTape.onWrite_goes</a> · 63 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.store_goes">Connection.Execution.NodeTape.store_goes</a> ↪ · 25 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.onClose_goes">Connection.Execution.NodeTape.onClose_goes</a> ↪ · 44 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.finish_goes"></a>▫️ <a href="../../app/Proofs.lean#L2653">Connection.Execution.NodeTape.finish_goes</a> · 43 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sealRetries_goes"></a>▫️ <a href="../../app/Proofs.lean#L2648">Connection.Execution.NodeTape.sealRetries_goes</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.seal_goes"></a>▫️ <a href="../../app/Proofs.lean#L2646">Connection.Execution.NodeTape.seal_goes</a> · 34 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
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
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.seal_goes">Connection.Execution.NodeTape.seal_goes</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.endSession_goes"></a>▫️ <a href="../../app/Proofs.lean#L2651">Connection.Execution.NodeTape.endSession_goes</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.effectsPurge_goes"></a>▫️ <a href="../../app/Proofs.lean#L2642">Connection.Execution.NodeTape.effectsPurge_goes</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.purge-"></a>▫️ <a href="../../app/Proofs.lean#L2501">Connection.Execution.GoesM.purge'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.flush_goes"></a>▫️ <a href="../../app/Proofs.lean#L2644">Connection.Execution.NodeTape.flush_goes</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.effectsPurge_goes">Connection.Execution.NodeTape.effectsPurge_goes</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.follow_goes"></a>▫️ <a href="../../app/Proofs.lean#L2639">Connection.Execution.NodeTape.follow_goes</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.open_goes"></a>▫️ <a href="../../app/Proofs.lean#L2636">Connection.Execution.NodeTape.open_goes</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.step_history_budget"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L20">Engine.step_history_budget</a> · 53 below</summary><ul>
<li><details><summary><a id="law-Engine.waits_history_bound"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L11">Engine.waits_history_bound</a> · 50 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.waitsOk_reach">Engine.waitsOk_reach</a> ↪ · 11 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.nodup_length_le">Engine.nodup_length_le</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.filter_lt">Engine.filter_lt</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.dedup_nodup"></a>🪜 <a href="../../engine/sync/ClosureStore.lean#L143">Engine.Sync.dedup_nodup</a> · 31 below · a step of App.stash_use, App.withNav_cache, Data.draftIn_newest +10</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.recordGiven_goes"></a>▫️ <a href="../../app/Proofs.lean#L2622">Connection.Execution.NodeTape.recordGiven_goes</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.put_goes">Connection.Execution.NodeTape.put_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.filedGive_reads"></a>▫️ <a href="../../app/Proofs.lean#L2602">Connection.Execution.NodeTape.filedGive_reads</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.give_reads">Connection.Execution.NodeTape.give_reads</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.filed_reads"></a>▫️ <a href="../../app/Proofs.lean#L2571">Connection.Execution.NodeTape.filed_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.GoesM.forIn-"></a>▫️ <a href="../../app/Proofs.lean#L2483">Connection.Execution.GoesM.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.refresh_reads"></a>▫️ <a href="../../app/Proofs.lean#L2626">Connection.Execution.NodeTape.refresh_reads</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.GoesM.bind-"></a>▫️ <a href="../../app/Proofs.lean#L2480">Connection.Execution.GoesM.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.goesM"></a>▫️ <a href="../../app/Proofs.lean#L2475">Engine.Sync.Reads.goesM</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.write_goes"></a>▫️ <a href="../../app/Proofs.lean#L2618">Connection.Execution.NodeTape.write_goes</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.getOp-"></a>▫️ <a href="../../app/Proofs.lean#L2495">Connection.Execution.GoesM.getOp'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.turn-"></a>▫️ <a href="../../app/Proofs.lean#L2499">Connection.Execution.GoesM.turn'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2479">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.read_program"></a>▫️ <a href="../../app/Proofs.lean#L2559">Connection.Execution.NodeTape.read_program</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.holdsIn_reads"></a>▫️ <a href="../../app/Proofs.lean#L2566">Connection.Execution.NodeTape.holdsIn_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
</ul>
