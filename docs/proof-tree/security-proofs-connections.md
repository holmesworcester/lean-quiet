# Security proofs › Connections

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Security proofs › Connections**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1377) · 🌐 world: the node's code in a World (69) · 🪜 step: a step of a wired law (57) · 📐 model: over a model (69) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2175)

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
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1325">Community.all2_cons2</a></li>
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
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Connection.meV_node"></a>✅ <a href="../../app/connection/Proofs.lean#L256">Connection.meV_node</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1712">Community.connect_iff</a> · 117 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.letIn_iff">Community.letIn_iff</a> ↪ · 114 below</li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1557">Community.Trusted.admitted</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1748">Community.byKey_args</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.deviceLive_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1046">Community.deviceLive_iff</a> · 62 below</summary><ul>
<li>✅ <a href="#law-Community.removals_iff">Community.removals_iff</a> ↪ · 55 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li><details><summary><a id="law-Community.unremoved_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1003">Community.unremoved_iff</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Proofs.lean#L990">Community.mem_cons_rowK</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1707">Community.byDevice_args</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.trusted_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1497">Community.trusted_iff</a> · 105 below</summary><ul>
<li><details><summary><a id="law-Community.approvedBy_true"></a>▫️ <a href="../../app/community/Proofs.lean#L1450">Community.approvedBy_true</a> · 104 below</summary><ul>
<li>✅ <a href="#law-Community.counts_iff">Community.counts_iff</a> ↪ · 103 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.factIn_req"></a>▫️ <a href="../../app/community/Proofs.lean#L1161">Community.factIn_req</a> · 59 below</summary><ul>
<li><details><summary><a id="law-Community.factIn_rows"></a>▫️ <a href="../../app/community/Proofs.lean#L1133">Community.factIn_rows</a> · 57 below</summary><ul>
<li><details><summary><a id="law-Community.mem_rows"></a>▫️ <a href="../../app/community/Family.lean#L1758">Community.mem_rows</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_rows_rel"></a>▫️ <a href="../../engine/core/Decl.lean#L219">Engine.mem_rows_rel</a> · 51 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_rows_all">Engine.mem_rows_all</a> ↪ · 4 below</li>
</ul></details></li>
<li>✅ <a href="../../app/community/Family.lean#L1655">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1657">Community.rels_short</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1116">Community.factIn_of_mem</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1104">Community.factIn_some</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1099">Community.byRequester_args</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.mem_rows">Community.mem_rows</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1707">Community.byDevice_args</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1099">Community.byRequester_args</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1104">Community.factIn_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.counts_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1417">Community.counts_iff</a> · 103 below</summary><ul>
<li>✅ <a href="#law-Community.kept_iff">Community.kept_iff</a> ↪ · 97 below</li>
<li>▫️ <a href="#law-Community.factIn_req">Community.factIn_req</a> ↪ · 59 below</li>
<li>✅ <a href="#law-Community.approval_links">Community.approval_links</a> ↪ · 50 below</li>
<li><details><summary><a id="law-Community.counts_inv"></a>▫️ <a href="../../app/community/Proofs.lean#L1402">Community.counts_inv</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.kept_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1387">Community.kept_iff</a> · 97 below</summary><ul>
<li><details><summary><a id="law-Community.usersKeep_iff"></a>▫️ <a href="../../app/community/Proofs.lean#L1317">Community.usersKeep_iff</a> · 93 below</summary><ul>
<li><details><summary><a id="law-Community.cutsKeep_iff"></a>▫️ <a href="../../app/community/Proofs.lean#L1298">Community.cutsKeep_iff</a> · 92 below</summary><ul>
<li>✅ <a href="#law-Community.inCut_iff">Community.inCut_iff</a> ↪ · 89 below</li>
<li>▫️ <a href="#law-Community.mem_rows">Community.mem_rows</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/member/remove/Proofs.lean#L16">Community.byUser_args</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1274">Community.cutsKeep_true</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.mem_rows">Community.mem_rows</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/member/remove/Proofs.lean#L16">Community.byUser_args</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1707">Community.byDevice_args</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.inCut_iff"></a>✅ <a href="../../app/community/Proofs.lean#L1261">Community.inCut_iff</a> · 89 below</summary><ul>
<li><details><summary><a id="law-Community.behindIn_iff"></a>▫️ <a href="../../app/community/Proofs.lean#L1187">Community.behindIn_iff</a> · 84 below</summary><ul>
<li><details><summary><a id="law-Community.behind_le"></a>▫️ <a href="../../app/community/Proofs.lean#L1168">Community.behind_le</a> · 59 below</summary><ul>
<li>✅ <a href="#law-Community.approval_links">Community.approval_links</a> ↪ · 50 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.factIn_dev"></a>▫️ <a href="../../app/community/Proofs.lean#L1155">Community.factIn_dev</a> · 59 below</summary><ul>
<li>▫️ <a href="#law-Community.factIn_rows">Community.factIn_rows</a> ↪ · 57 below</li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1095">Community.byDev_args</a></li>
</ul></details></li>
<li>✅ <a href="#law-Community.approval_links">Community.approval_links</a> ↪ · 50 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Community.behind_le">Community.behind_le</a> ↪ · 59 below</li>
<li>✅ <a href="#law-Community.removal_cut">Community.removal_cut</a> ↪ · 48 below</li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1244">Community.inCut_true</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.refuse_nonmember"></a>✅ <a href="../../app/community/Proofs.lean#L1726">Community.refuse_nonmember</a> · 119 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1557">Community.Trusted.admitted</a></li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L21">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_approved"></a>✅ <a href="../../app/community/Proofs.lean#L1766">Community.connect_approved</a> · 122 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admission_approved">Community.admission_approved</a> ↪ · 59 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1557">Community.Trusted.admitted</a></li>
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
<li><details><summary><a id="law-Community.connect_agree"></a>✅ <a href="../../app/community/Proofs.lean#L1820">Community.connect_agree</a> · 118 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.connect_iff_trace"></a>🌐 <a href="../../app/Proofs.lean#L2870">Connection.Execution.connect_iff_trace</a> · 344 below</summary><ul>
<li>🌐 <a href="quality-proofs-the-engine.md#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 222 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.connect_iff_node">Connection.connect_iff_node</a> ↪ · 167 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.refuse_nonmember_trace"></a>🌐 <a href="../../app/Proofs.lean#L2887">Connection.Execution.refuse_nonmember_trace</a> · 346 below</summary><ul>
<li>🌐 <a href="quality-proofs-the-engine.md#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 222 below</li>
<li><details><summary><a id="law-Connection.refuse_nonmember_node"></a>✅ <a href="../../app/connection/Proofs.lean#L470">Connection.refuse_nonmember_node</a> · 169 below</summary><ul>
<li>✅ <a href="#law-Community.refuse_nonmember">Community.refuse_nonmember</a> ↪ · 119 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li><details><summary><a id="law-Community.reads_allowPeer"></a>✅ <a href="../../app/connection/Family.lean#L670">Community.reads_allowPeer</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.reads_letIn">Community.reads_letIn</a> ↪ · 9 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.removal_cuts_off"></a>✅ <a href="../../app/community/Proofs.lean#L1838">Community.removal_cuts_off</a> · 120 below</summary><ul>
<li>✅ <a href="#law-Community.refuse_nonmember">Community.refuse_nonmember</a> ↪ · 119 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.cut_stays"></a>✅ <a href="../../app/community/member/remove/Proofs.lean#L30">Community.cut_stays</a> · 9 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L21">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.cut_consented"></a>✅ <a href="../../app/community/member/Proofs.lean#L146">Community.cut_consented</a> · 48 below</summary><ul>
<li>✅ <a href="#law-Community.endpoint_signed">Community.endpoint_signed</a> ↪ · 47 below</li>
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
<li><details><summary><a id="law-Community.removals_iff"></a>✅ <a href="../../app/community/Proofs.lean#L948">Community.removals_iff</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li><details><summary><a id="law-Engine.total_pos"></a>▫️ <a href="../../engine/core/Decl.lean#L188">Engine.total_pos</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/member/remove/Proofs.lean#L16">Community.byUser_args</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removal_authorized">Community.removal_authorized</a> ↪ · 48 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Connection.Execution.removal_cuts_off_trace"></a>🌐 <a href="../../app/Proofs.lean#L2878">Connection.Execution.removal_cuts_off_trace</a> · 347 below</summary><ul>
<li>🌐 <a href="quality-proofs-the-engine.md#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 222 below</li>
<li><details><summary><a id="law-Connection.removal_cuts_off_node"></a>✅ <a href="../../app/connection/Proofs.lean#L642">Connection.removal_cuts_off_node</a> · 170 below</summary><ul>
<li>✅ <a href="#law-Community.removal_cuts_off">Community.removal_cuts_off</a> ↪ · 120 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>✅ <a href="#law-Community.reads_allowPeer">Community.reads_allowPeer</a> ↪ · 10 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.removed_trace"></a>🌐 <a href="../../app/Proofs.lean#L2902">Connection.Execution.removed_trace</a> · 268 below</summary><ul>
<li>🌐 <a href="quality-proofs-the-engine.md#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 222 below</li>
<li><details><summary><a id="law-Connection.removed_node"></a>✅ <a href="../../app/Proofs.lean#L1102">Connection.removed_node</a> · 81 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.no_self_readmission"></a>✅ <a href="../../app/community/Proofs.lean#L1886">Community.no_self_readmission</a> · 121 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
<li>✅ <a href="#law-Community.outside_cut_admits_none">Community.outside_cut_admits_none</a> ↪ · 10 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L21">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.outside_cut_admits_none"></a>✅ <a href="../../app/community/Proofs.lean#L1871">Community.outside_cut_admits_none</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Community.counts_above"></a>▫️ <a href="../../app/community/Proofs.lean#L1859">Community.counts_above</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Community.counts_inv">Community.counts_inv</a> ↪ · 8 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Community.counts_inv">Community.counts_inv</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.inside_cut_stays"></a>✅ <a href="../../app/community/Proofs.lean#L1910">Community.inside_cut_stays</a> · 7 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.removeMember_keeps"></a>✅ <a href="../../app/community/Proofs.lean#L2054">Community.removeMember_keeps</a> · 133 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Community.removeMember_valid">Community.removeMember_valid</a> ↪ · 89 below</li>
<li><details><summary><a id="law-Community.first_after"></a>▫️ <a href="../../app/community/Family.lean#L1851">Community.first_after</a> · 75 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li><details><summary><a id="law-Engine.top_max"></a>✅ <a href="../../engine/core/Order.lean#L173">Engine.top_max</a> · 21 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.sortPos_sorted">Engine.sortPos_sorted</a> ↪ · 15 below</li>
<li><details><summary><a id="law-Engine.sorted_last"></a>▫️ <a href="../../engine/core/Order.lean#L157">Engine.sorted_last</a> · 10 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1628">Community.matching_also_nil</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li><details><summary><a id="law-Community.behind_of_unforked"></a>▫️ <a href="../../app/community/Proofs.lean#L1978">Community.behind_of_unforked</a> · 51 below</summary><ul>
<li>✅ <a href="#law-Community.approval_links">Community.approval_links</a> ↪ · 50 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.check_removal">Community.check_removal</a> ↪ · 25 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li><details><summary><a id="law-Community.mem_cutOf"></a>▫️ <a href="../../app/community/Proofs.lean#L2026">Community.mem_cutOf</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Community.behind_stays"></a>▫️ <a href="../../app/community/Proofs.lean#L1970">Community.behind_stays</a> · 7 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Community.lexCmp_be64"></a>✅ <a href="../../app/community/Family.lean#L1829">Community.lexCmp_be64</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.lexCmp_digits"></a>▫️ <a href="../../app/community/Family.lean#L1797">Community.lexCmp_digits</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/community/Family.lean#L1780">Community.compare_place</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1775">Community.digit_toNat</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1820">Community.be64_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.bcmp_eq_lexCmp"></a>▫️ <a href="../../engine/core/Query.lean#L136">Engine.bcmp_eq_lexCmp</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmpFrom_eq"></a>▫️ <a href="../../engine/core/Query.lean#L117">Engine.bcmpFrom_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Query.lean#L113">Engine.drop_data_cons</a></li>
<li>▫️ <a href="../../engine/core/Query.lean#L110">Engine.drop_data_nil</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.headsOf_mem"></a>▫️ <a href="../../app/community/Proofs.lean#L1995">Community.headsOf_mem</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.removeMember_reqs"></a>▫️ <a href="../../app/community/Proofs.lean#L814">Community.removeMember_reqs</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1689">Community.admission_byUser_args</a></li>
<li>▫️ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L21">Community.all2_cons3</a></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L1095">Community.byDev_args</a></li>
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
<li><details><summary><a id="law-Community.trust_order_free"></a>✅ <a href="../../app/community/Proofs.lean#L1942">Community.trust_order_free</a> · 175 below</summary><ul>
<li>✅ <a href="#law-Community.trust_agree">Community.trust_agree</a> ↪ · 119 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.trust_agree"></a>✅ <a href="../../app/community/Proofs.lean#L1924">Community.trust_agree</a> · 119 below</summary><ul>
<li>✅ <a href="#law-Community.connect_agree">Community.connect_agree</a> ↪ · 118 below</li>
<li>✅ <a href="#law-Community.trusted_iff">Community.trusted_iff</a> ↪ · 105 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.approval_links"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L101">Community.approval_links</a> · 50 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.approval_reqs">Community.approval_reqs</a> ↪ · 47 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L27">Community.all2_one</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1321">Community.all2_two</a></li>
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
<li><details><summary><a id="law-Community.removal_cut"></a>✅ <a href="../../app/community/Proofs.lean#L1232">Community.removal_cut</a> · 48 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.check_removal">Community.check_removal</a> ↪ · 25 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L21">Community.all2_cons3</a></li>
<li>▫️ <a href="../../app/community/member/Proofs.lean#L37">Community.cutOf_mem</a></li>
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
<li><details><summary><a id="law-Community.mine_not_removed"></a>✅ <a href="../../app/community/Proofs.lean#L2368">Community.mine_not_removed</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Community.standing_some"></a>▫️ <a href="../../app/community/Proofs.lean#L2265">Community.standing_some</a> · 68 below</summary><ul>
<li>✅ <a href="#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li><details><summary><a id="law-Community.not_admitted_of_empty"></a>▫️ <a href="../../app/community/Proofs.lean#L2226">Community.not_admitted_of_empty</a> · 56 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1707">Community.byDevice_args</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.standing_eval"></a>▫️ <a href="../../app/community/Proofs.lean#L2246">Community.standing_eval</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.deviceLive_eval"></a>▫️ <a href="../../app/community/Proofs.lean#L2216">Community.deviceLive_eval</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1764">Community.eval_list</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.pick_some"></a>▫️ <a href="../../app/community/Proofs.lean#L2295">Community.pick_some</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1767">Community.better_cases</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.rejoin_fresh"></a>✅ <a href="../../app/community/Proofs.lean#L2391">Community.rejoin_fresh</a> · 77 below</summary><ul>
<li><details><summary><a id="law-Community.standing_cut"></a>▫️ <a href="../../app/community/Proofs.lean#L2278">Community.standing_cut</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li>▫️ <a href="#law-Community.not_admitted_of_empty">Community.not_admitted_of_empty</a> ↪ · 56 below</li>
<li>▫️ <a href="#law-Community.standing_eval">Community.standing_eval</a> ↪ · 4 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L21">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.admitted_total"></a>▫️ <a href="../../app/community/Proofs.lean#L2234">Community.admitted_total</a> · 55 below</summary><ul>
<li><details><summary><a id="law-Engine.total_rel"></a>▫️ <a href="../../engine/core/Decl.lean#L231">Engine.total_rel</a> · 51 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>▫️ <a href="#law-Engine.total_pos">Engine.total_pos</a> ↪ · 4 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1707">Community.byDevice_args</a></li>
<li>✅ <a href="../../app/community/Family.lean#L1655">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1657">Community.rels_short</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.mem_rows">Community.mem_rows</a> ↪ · 54 below</li>
<li><details><summary><a id="law-Community.dormant_none"></a>▫️ <a href="../../app/community/member/join/joining/Proofs.lean#L10">Community.dormant_none</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.nodeKeyOr_held"></a>▫️ <a href="../../app/community/device/endpoint/Proofs.lean#L40">Community.nodeKeyOr_held</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.pick_none"></a>▫️ <a href="../../app/community/Proofs.lean#L2347">Community.pick_none</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1764">Community.eval_list</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.join_new_device"></a>✅ <a href="../../app/community/Proofs.lean#L2427">Community.join_new_device</a> · 73 below</summary><ul>
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
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1764">Community.eval_list</a></li>
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
<li><details><summary><a id="law-Community.removed_stays_removed"></a>✅ <a href="../../app/community/Proofs.lean#L2474">Community.removed_stays_removed</a> · 122 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 117 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L21">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rejoin_dials"></a>✅ <a href="../../app/Proofs.lean#L1005">Connection.rejoin_dials</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Connection.dialAll_mem"></a>▫️ <a href="../../app/Proofs.lean#L985">Connection.dialAll_mem</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.dialOne_state"></a>✅ <a href="../../app/Proofs.lean#L928">Connection.dialOne_state</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Connection.requestOf_state"></a>✅ <a href="../../app/connection/Proofs.lean#L436">Connection.requestOf_state</a> · 29 below</summary><ul>
<li><details><summary><a id="law-Connection.helloOf_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L431">Connection.helloOf_state</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Connection.run_view"></a>▫️ <a href="../../app/connection/Proofs.lean#L204">Connection.run_view</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/View.lean#L55">Engine.View.run_model</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L196">Connection.run_rows</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dialOne_sends"></a>✅ <a href="../../app/Proofs.lean#L917">Connection.dialOne_sends</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.dialOne_sends_mem"></a>✅ <a href="../../app/Proofs.lean#L847">Connection.dialOne_sends_mem</a> · 34 below</summary><ul>
<li>✅ <a href="#law-Connection.requestOf_state">Connection.requestOf_state</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L196">Connection.run_rows</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.reconnect_dials"></a>✅ <a href="../../app/Proofs.lean#L1027">Connection.reconnect_dials</a> · 38 below</summary><ul>
<li>▫️ <a href="#law-Connection.dialAll_mem">Connection.dialAll_mem</a> ↪ · 35 below</li>
<li>✅ <a href="#law-Connection.dialOne_sends">Connection.dialOne_sends</a> ↪ · 35 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.entry_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L963">Engine.Sync.entry_fresh</a> · 95 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onTick_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L882">Engine.Sync.onTick_fresh</a> · 86 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onTickReserved_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L844">Engine.Sync.onTickReserved_fresh</a> · 84 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L688">Engine.Sync.finish_ok</a> · 51 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.sweepAll_ok"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L812">Engine.Sync.sweepAll_ok</a> · 14 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.give_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L230">Engine.Sync.give_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.closureOps_reads">Engine.Sync.closureOps_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L277">Engine.Sync.tick_reads</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L159">Engine.Sync.ReadOnly.afterActs</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onTickDirect_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L769">Engine.Sync.onTickDirect_fresh</a> · 83 below</summary><ul>
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
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onFrame_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L926">Engine.Sync.onFrame_fresh</a> · 83 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onSealed_fresh"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L891">Engine.Sync.onSealed_fresh</a> · 82 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.apply_ok">Engine.Sync.apply_ok</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Engine.Sync.FramesOk.empty"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L744">Engine.Sync.FramesOk.empty</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.onHold_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L204">Engine.Sync.onHold_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.holdsIn_reads">Engine.Sync.holdsIn_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
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
<li><details><summary><a id="law-Engine.Sync.onWrite_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L750">Engine.Sync.onWrite_fresh</a> · 71 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 30 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onClose_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L761">Engine.Sync.onClose_fresh</a> · 52 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L194">Engine.Sync.ActsOk.noConn</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_cut_node"></a>✅ <a href="../../app/Proofs.lean#L1153">Connection.rooms_cut_node</a> · 179 below</summary><ul>
<li>✅ <a href="#law-Connection.removal_cuts_off_node">Connection.removal_cuts_off_node</a> ↪ · 170 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.connect_iff_node">Connection.connect_iff_node</a> ↪ · 167 below</li>
<li>✅ <a href="#law-Connection.rooms_cut">Connection.rooms_cut</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_trusted"></a>✅ <a href="../../app/Proofs.lean#L1111">Connection.rooms_trusted</a> · 4 below</summary><ul>
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
<li><details><summary><a id="law-Connection.rooms_cut"></a>✅ <a href="../../app/Proofs.lean#L1133">Connection.rooms_cut</a> · 7 below</summary><ul>
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
<li>▫️ <a href="../../app/connection/Proofs.lean#L207">Connection.has_of_mem</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.openSessions_state">Connection.openSessions_state</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Connection.allSessions_established"></a>▫️ <a href="../../app/Proofs.lean#L346">Connection.allSessions_established</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Connection.mem_sessionsOf"></a>▫️ <a href="../../app/Proofs.lean#L324">Connection.mem_sessionsOf</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L307">Connection.sessionOf_some</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L231">Connection.sessionOf_state</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.allSessions_state">Connection.allSessions_state</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.carrying_mem">Connection.carrying_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.trusts_live"></a>✅ <a href="../../app/Proofs.lean#L113">Connection.trusts_live</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L222">Connection.eval_liftL_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_model"></a>✅ <a href="../../app/Proofs.lean#L1167">Connection.rooms_model</a> · 1 below</summary><ul>
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
<li><details><summary><a id="law-Connection.removal_reaches_session"></a>✅ <a href="../../app/Proofs.lean#L3014">Connection.removal_reaches_session</a> · 230 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.entry_fresh">Engine.Sync.entry_fresh</a> ↪ · 95 below</li>
<li><details><summary><a id="law-Connection.hooks_readOnly"></a>✅ <a href="../../app/Proofs.lean#L2962">Connection.hooks_readOnly</a> · 84 below</summary><ul>
<li><details><summary><a id="law-Connection.hooks_reads"></a>✅ <a href="../../app/Proofs.lean#L2150">Connection.hooks_reads</a> · 83 below</summary><ul>
<li><details><summary><a id="law-Connection.react_reads"></a>▫️ <a href="../../app/Proofs.lean#L2059">Connection.react_reads</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2037">Connection.answerAll_reads</a> · 45 below</summary><ul>
<li>▫️ <a href="#law-Connection.answerOne_reads">Connection.answerOne_reads</a> ↪ · 44 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2055">Connection.establishAll_reads</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.establishReqs_reads">Connection.establishReqs_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2016">Connection.openAll_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Connection.openEach_reads">Connection.openEach_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.deliverAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2024">Connection.deliverAll_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.joinsOf_reads">Connection.joinsOf_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.endpoints_reads"></a>▫️ <a href="../../app/Proofs.lean#L1992">Connection.endpoints_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L168">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.onArrival_reads"></a>▫️ <a href="../../app/Proofs.lean#L2138">Connection.onArrival_reads</a> · 44 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.count_reads"></a>▫️ <a href="../../app/Proofs.lean#L1989">Connection.count_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L168">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.resendConns_reads"></a>▫️ <a href="../../app/Proofs.lean#L2134">Connection.resendConns_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.view_reads"></a>▫️ <a href="../../app/Proofs.lean#L1981">Connection.view_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L168">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dial_reads"></a>▫️ <a href="../../app/Proofs.lean#L2086">Connection.dial_reads</a> · 41 below</summary><ul>
<li><details><summary><a id="law-Connection.dialAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2081">Connection.dialAll_reads</a> · 39 below</summary><ul>
<li>▫️ <a href="#law-Connection.dialOne_reads">Connection.dialOne_reads</a> ↪ · 38 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.endpoints_reads">Connection.endpoints_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L168">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retired_reads"></a>▫️ <a href="../../app/Proofs.lean#L2120">Connection.retired_reads</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Connection.openSessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2112">Connection.openSessions_reads</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Connection.allSessions_reads">Connection.allSessions_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Connection.carrying_reads">Connection.carrying_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2115">Connection.sessions_reads</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Connection.openSessions_reads">Connection.openSessions_reads</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.outbox_reads"></a>▫️ <a href="../../app/Proofs.lean#L2131">Connection.outbox_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sealFor_reads"></a>▫️ <a href="../../app/Proofs.lean#L2123">Connection.sealFor_reads</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Connection.keys_reads"></a>▫️ <a href="../../app/Proofs.lean#L2001">Connection.keys_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.frameOpen_reads"></a>▫️ <a href="../../app/Proofs.lean#L2128">Connection.frameOpen_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.keys_reads">Connection.keys_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retryKey_reads"></a>▫️ <a href="../../app/Proofs.lean#L2142">Connection.retryKey_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_reads"></a>▫️ <a href="../../app/Proofs.lean#L2095">Connection.rooms_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.closing_reads"></a>▫️ <a href="../../app/Proofs.lean#L2092">Connection.closing_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sent_mayGo"></a>✅ <a href="../../app/Proofs.lean#L2976">Connection.sent_mayGo</a> · 84 below</summary><ul>
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
<li><details><summary><a id="law-Connection.rooms_held"></a>✅ <a href="../../app/Proofs.lean#L1974">Connection.rooms_held</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Proofs.lean#L1967">Connection.view_held</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.FramesBy.mono"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L677">Engine.Sync.FramesBy.mono</a> · 28 below</summary><ul>
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
<li>▫️ <a href="../../app/connection/Proofs.lean#L304">Connection.run_arrivedFrom</a></li>
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
<li>▫️ <a href="../../app/connection/Proofs.lean#L304">Connection.run_arrivedFrom</a></li>
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
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Connection.establishAll_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L400">Connection.establishAll_body</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Connection.establishReqs_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L383">Connection.establishReqs_body</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Connection.establishConns_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L369">Connection.establishConns_body</a> · 38 below</summary><ul>
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
<li><details><summary><a id="law-Connection.openAll_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L360">Connection.openAll_body</a> · 39 below</summary><ul>
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
<li><details><summary><a id="law-Connection.openAll_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L354">Connection.openAll_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L347">Connection.openEach_state</a></li>
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
<li><details><summary><a id="law-Connection.receiptFor_receipts"></a>▫️ <a href="../../app/connection/Proofs.lean#L412">Connection.receiptFor_receipts</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L222">Connection.eval_liftL_bind</a></li>
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
<li><details><summary><a id="law-Connection.establishAll_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L335">Connection.establishAll_conn</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.establishReqs_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L319">Connection.establishReqs_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L306">Connection.establishConns_conn</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L295">Connection.openAll_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L282">Connection.openEach_conn</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/connection/Proofs.lean#L274">Connection.room_connOp</a></li>
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
<li><details><summary><a id="law-Community.local_fact_mine"></a>✅ <a href="../../app/community/Family.lean#L1509">Community.local_fact_mine</a> · 59 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>✅ <a href="#law-Engine.stored_local">Engine.stored_local</a> ↪ · 13 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L704">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1490">Community.check_local</a></li>
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
<li>✅ <a href="#law-Community.local_fact_mine">Community.local_fact_mine</a> ↪ · 59 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.message_authorized">Community.message_authorized</a> ↪ · 48 below</li>
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
<li><details><summary><a id="law-Connection.sealFor_opens"></a>✅ <a href="../../app/connection/Proofs.lean#L592">Connection.sealFor_opens</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Connection.open_seal_sodium">Connection.open_seal_sodium</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/core/Crypto.lean#L36">Engine.Bytes.of?_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.open_seal_sodium"></a>✅ <a href="../../app/connection/Proofs.lean#L572">Connection.open_seal_sodium</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.open_seal">Connection.open_seal</a> ↪ · 1 below</li>
<li>✅ <a href="../../app/connection/Proofs.lean#L562">Connection.ad_fits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.cid_seal_sodium"></a>✅ <a href="../../app/connection/Proofs.lean#L580">Connection.cid_seal_sodium</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.cid_seal">Connection.cid_seal</a> ↪ · 1 below</li>
<li>✅ <a href="../../app/connection/Proofs.lean#L562">Connection.ad_fits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.open_seal"></a>✅ <a href="../../app/connection/Proofs.lean#L516">Connection.open_seal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L509">Connection.seal_parts</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.cid_seal"></a>✅ <a href="../../app/connection/Proofs.lean#L545">Connection.cid_seal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L509">Connection.seal_parts</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L467">Engine.Sync.mem_bundles</a></li>
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
<li><details><summary><a id="law-Engine.Sync.filedGive_reads"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L240">Engine.Sync.filedGive_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filed_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L197">Engine.Sync.filed_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.give_reads">Engine.Sync.give_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closureOps_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L208">Engine.Sync.closureOps_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.holdsIn_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L201">Engine.Sync.holdsIn_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.forIn-"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L159">Engine.Sync.Reads.forIn'</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.answerOne_reads"></a>▫️ <a href="../../app/Proofs.lean#L2032">Connection.answerOne_reads</a> · 44 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.arrivedFrom_reads"></a>▫️ <a href="../../app/Proofs.lean#L1995">Connection.arrivedFrom_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishReqs_reads"></a>▫️ <a href="../../app/Proofs.lean#L2050">Connection.establishReqs_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.establishConns_reads"></a>▫️ <a href="../../app/Proofs.lean#L2046">Connection.establishConns_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rows_reads"></a>▫️ <a href="../../app/Proofs.lean#L1986">Connection.rows_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L168">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openEach_reads"></a>▫️ <a href="../../app/Proofs.lean#L2012">Connection.openEach_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.joinsOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2020">Connection.joinsOf_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dialOne_reads"></a>▫️ <a href="../../app/Proofs.lean#L2076">Connection.dialOne_reads</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Connection.requestOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2067">Connection.requestOf_reads</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Connection.helloOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2007">Connection.helloOf_reads</a> · 32 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.connectedTo_reads"></a>▫️ <a href="../../app/Proofs.lean#L2004">Connection.connectedTo_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L168">Engine.Sync.Reads.list'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.allSessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2105">Connection.allSessions_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionsOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2101">Connection.sessionsOf_reads</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2098">Connection.sessionOf_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.arrival_reads"></a>▫️ <a href="../../app/Proofs.lean#L1998">Connection.arrival_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L166">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.carrying_reads"></a>▫️ <a href="../../app/Proofs.lean#L2108">Connection.carrying_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
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
</ul>
