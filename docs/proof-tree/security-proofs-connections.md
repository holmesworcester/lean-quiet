# Security proofs › Connections

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Security proofs › Connections**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1075) · 🌐 world: the node's code in a World (35) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (299) · 🧪 control: a negative control (25) · ▫️ lemma: not audited (1984)

<ul>
<li><details><summary><a id="law-Connection.opened_endpoint"></a>✅ <a href="../../app/Proofs.lean#L394">Connection.opened_endpoint</a> · 29 below</summary><ul>
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
<li><details><summary><a id="law-Connection.established_endpoint"></a>✅ <a href="../../app/Proofs.lean#L423">Connection.established_endpoint</a> · 29 below</summary><ul>
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
<li><details><summary><a id="law-Community.endpoint_signed"></a>✅ <a href="../../app/community/member/invite/request/Proofs.lean#L68">Community.endpoint_signed</a> · 47 below</summary><ul>
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
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1222">Community.all2_cons2</a></li>
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
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Connection.meV_node"></a>✅ <a href="../../app/connection/Proofs.lean#L223">Connection.meV_node</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.new_device_trusted"></a>✅ <a href="../../app/community/Proofs.lean#L934">Community.new_device_trusted</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_iff"></a>✅ <a href="../../app/community/Proofs.lean#L821">Community.connect_iff</a> · 68 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.live_iff">Community.live_iff</a> ↪ · 66 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1566">Community.byKey_args</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.deviceLive_iff"></a>✅ <a href="../../app/community/Proofs.lean#L711">Community.deviceLive_iff</a> · 62 below</summary><ul>
<li>✅ <a href="#law-Community.removals_iff">Community.removals_iff</a> ↪ · 55 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li><details><summary><a id="law-Community.unremoved_iff"></a>✅ <a href="../../app/community/Proofs.lean#L668">Community.unremoved_iff</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/Proofs.lean#L655">Community.mem_cons_row</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1525">Community.byDevice_args</a></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.refuse_nonmember"></a>✅ <a href="../../app/community/Proofs.lean#L834">Community.refuse_nonmember</a> · 70 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L40">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.connect_approved"></a>✅ <a href="../../app/community/Proofs.lean#L860">Community.connect_approved</a> · 88 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admission_approved">Community.admission_approved</a> ↪ · 46 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.connect_agree"></a>✅ <a href="../../app/community/Proofs.lean#L900">Community.connect_agree</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.removal_cuts_off"></a>✅ <a href="../../app/community/Proofs.lean#L918">Community.removal_cuts_off</a> · 71 below</summary><ul>
<li>✅ <a href="#law-Community.refuse_nonmember">Community.refuse_nonmember</a> ↪ · 70 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.cut_stays"></a>✅ <a href="../../app/community/member/remove/Proofs.lean#L49">Community.cut_stays</a> · 9 below</summary><ul>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L40">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.cut_consented"></a>✅ <a href="../../app/community/member/Proofs.lean#L113">Community.cut_consented</a> · 48 below</summary><ul>
<li>✅ <a href="#law-Community.endpoint_signed">Community.endpoint_signed</a> ↪ · 47 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Community.removals_iff"></a>✅ <a href="../../app/community/Proofs.lean#L625">Community.removals_iff</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li><details><summary><a id="law-Engine.total_pos"></a>▫️ <a href="../../engine/core/Decl.lean#L188">Engine.total_pos</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/member/remove/Proofs.lean#L35">Community.byUser_args</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removal_authorized">Community.removal_authorized</a> ↪ · 47 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Community.mine_not_removed"></a>✅ <a href="../../app/community/Proofs.lean#L1206">Community.mine_not_removed</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Community.standing_some"></a>▫️ <a href="../../app/community/Proofs.lean#L1103">Community.standing_some</a> · 68 below</summary><ul>
<li>✅ <a href="#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li><details><summary><a id="law-Community.not_admitted_of_empty"></a>▫️ <a href="../../app/community/Proofs.lean#L1064">Community.not_admitted_of_empty</a> · 56 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.exists_row">Community.exists_row</a> ↪ · 54 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1525">Community.byDevice_args</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.standing_eval"></a>▫️ <a href="../../app/community/Proofs.lean#L1084">Community.standing_eval</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.deviceLive_eval"></a>▫️ <a href="../../app/community/Proofs.lean#L1054">Community.deviceLive_eval</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1582">Community.eval_list</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.pick_some"></a>▫️ <a href="../../app/community/Proofs.lean#L1133">Community.pick_some</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1585">Community.better_cases</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.rejoin_fresh"></a>✅ <a href="../../app/community/Proofs.lean#L1229">Community.rejoin_fresh</a> · 77 below</summary><ul>
<li><details><summary><a id="law-Community.standing_cut"></a>▫️ <a href="../../app/community/Proofs.lean#L1116">Community.standing_cut</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li>▫️ <a href="#law-Community.not_admitted_of_empty">Community.not_admitted_of_empty</a> ↪ · 56 below</li>
<li>▫️ <a href="#law-Community.standing_eval">Community.standing_eval</a> ↪ · 4 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L40">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.admitted_total"></a>▫️ <a href="../../app/community/Proofs.lean#L1072">Community.admitted_total</a> · 55 below</summary><ul>
<li><details><summary><a id="law-Engine.total_rel"></a>▫️ <a href="../../engine/core/Decl.lean#L231">Engine.total_rel</a> · 51 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>▫️ <a href="#law-Engine.total_pos">Engine.total_pos</a> ↪ · 4 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1525">Community.byDevice_args</a></li>
<li>✅ <a href="../../app/community/Family.lean#L1473">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1475">Community.rels_short</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.mem_rows"></a>▫️ <a href="../../app/community/Family.lean#L1576">Community.mem_rows</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_rows_rel"></a>▫️ <a href="../../engine/core/Decl.lean#L219">Engine.mem_rows_rel</a> · 51 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_rows_all">Engine.mem_rows_all</a> ↪ · 4 below</li>
</ul></details></li>
<li>✅ <a href="../../app/community/Family.lean#L1473">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1475">Community.rels_short</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.dormant_none"></a>▫️ <a href="../../app/community/member/join/joining/Proofs.lean#L10">Community.dormant_none</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.nodeKeyOr_held"></a>▫️ <a href="../../app/community/device/endpoint/Proofs.lean#L40">Community.nodeKeyOr_held</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.pick_none"></a>▫️ <a href="../../app/community/Proofs.lean#L1185">Community.pick_none</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1582">Community.eval_list</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.join_new_device"></a>✅ <a href="../../app/community/Proofs.lean#L1265">Community.join_new_device</a> · 73 below</summary><ul>
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
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1582">Community.eval_list</a></li>
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
<li><details><summary><a id="law-Community.removed_stays_removed"></a>✅ <a href="../../app/community/Proofs.lean#L1312">Community.removed_stays_removed</a> · 73 below</summary><ul>
<li>✅ <a href="#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.removed_stays">Community.removed_stays</a> ↪ · 6 below</li>
<li>✅ <a href="../../app/community/member/remove/Proofs.lean#L40">Community.cut_not_live</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rejoin_dials"></a>✅ <a href="../../app/Proofs.lean#L1004">Connection.rejoin_dials</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Connection.dialAll_mem"></a>▫️ <a href="../../app/Proofs.lean#L984">Connection.dialAll_mem</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.dialOne_state"></a>✅ <a href="../../app/Proofs.lean#L927">Connection.dialOne_state</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Connection.requestOf_state"></a>✅ <a href="../../app/connection/Proofs.lean#L403">Connection.requestOf_state</a> · 29 below</summary><ul>
<li><details><summary><a id="law-Connection.helloOf_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L398">Connection.helloOf_state</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Connection.run_view"></a>▫️ <a href="../../app/connection/Proofs.lean#L171">Connection.run_view</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/View.lean#L55">Engine.View.run_model</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L163">Connection.run_rows</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dialOne_sends"></a>✅ <a href="../../app/Proofs.lean#L916">Connection.dialOne_sends</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.dialOne_sends_mem"></a>✅ <a href="../../app/Proofs.lean#L846">Connection.dialOne_sends_mem</a> · 34 below</summary><ul>
<li>✅ <a href="#law-Connection.requestOf_state">Connection.requestOf_state</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L163">Connection.run_rows</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.reconnect_dials"></a>✅ <a href="../../app/Proofs.lean#L1026">Connection.reconnect_dials</a> · 38 below</summary><ul>
<li>▫️ <a href="#law-Connection.dialAll_mem">Connection.dialAll_mem</a> ↪ · 35 below</li>
<li>✅ <a href="#law-Connection.dialOne_sends">Connection.dialOne_sends</a> ↪ · 35 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.entry_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L964">Engine.Sync.entry_fresh</a> · 102 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onTick_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L883">Engine.Sync.onTick_fresh</a> · 93 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onTickReserved_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L845">Engine.Sync.onTickReserved_fresh</a> · 91 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L689">Engine.Sync.finish_ok</a> · 51 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sealRetries_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L608">Engine.Sync.sealRetries_ok</a> · 33 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.seal_ok">Engine.Sync.seal_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Engine.Sync.SealedOk.mono">Engine.Sync.SealedOk.mono</a> ↪ · 28 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_ok">Engine.Sync.seal_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.follow_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L503">Engine.Sync.follow_ok</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.open_ok">Engine.Sync.open_ok</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L194">Engine.Sync.ActsOk.noConn</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.endSession_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L661">Engine.Sync.endSession_goes</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Goes.bind-">Engine.Sync.Goes.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.goes">Engine.Sync.Reads.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.effectsPurge_goes">Engine.Sync.effectsPurge_goes</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.flush_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L644">Engine.Sync.flush_ok</a> · 2 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.apply_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L444">Engine.Sync.apply_ok</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.store_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L410">Engine.Sync.store_ok</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.fanout_ok">Engine.Sync.fanout_ok</a> ↪ · 29 below</li>
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
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 31 below</li>
<li><details><summary><a id="law-Engine.Sync.sweepAll_ok"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L813">Engine.Sync.sweepAll_ok</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sweep_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L333">Engine.Sync.sweep_ok</a> · 6 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.tickGive_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L282">Engine.Sync.tickGive_reads</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.tick_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L277">Engine.Sync.tick_reads</a> · 8 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.walk_keeps">Engine.Sync.walk_keeps</a> ↪ · 5 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.give_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L187">Engine.Sync.give_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.closureOps_reads">Engine.Sync.closureOps_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L468">Engine.Sync.serveOwed_ok</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serveOwed_reads-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L290">Engine.Sync.serveOwed_reads'</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L168">Engine.Sync.ActsOk.empty</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L159">Engine.Sync.ReadOnly.afterActs</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onTickDirect_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L770">Engine.Sync.onTickDirect_fresh</a> · 90 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.apply_ok">Engine.Sync.apply_ok</a> ↪ · 34 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Engine.Sync.tickGive_reads">Engine.Sync.tickGive_reads</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_ok">Engine.Sync.serveOwed_ok</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.sweep_ok">Engine.Sync.sweep_ok</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.left">Engine.Sync.ActsOk.left</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.ActsOk.right">Engine.Sync.ActsOk.right</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L171">Engine.Sync.ActsOk.append</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L159">Engine.Sync.ReadOnly.afterActs</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L260">Engine.Sync.refresh_carry</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onFrame_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L927">Engine.Sync.onFrame_fresh</a> · 84 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onSealed_fresh"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L892">Engine.Sync.onSealed_fresh</a> · 83 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.apply_ok">Engine.Sync.apply_ok</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Engine.Sync.FramesOk.empty"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L745">Engine.Sync.FramesOk.empty</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.recv_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L286">Engine.Sync.recv_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onHold_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L161">Engine.Sync.onHold_reads</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.holdsIn_reads">Engine.Sync.holdsIn_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
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
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Engine.Sync.FramesOk.empty">Engine.Sync.FramesOk.empty</a> ↪ · 28 below</li>
<li><details><summary><a id="law-Engine.Sync.write_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L232">Engine.Sync.write_goes</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Goes.forIn-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L67">Engine.Sync.Goes.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L61">Engine.Sync.Goes.pure'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Goes.getOp-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L79">Engine.Sync.Goes.getOp'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.goes">Engine.Sync.Reads.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
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
<li><details><summary><a id="law-Engine.Sync.onWrite_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L751">Engine.Sync.onWrite_fresh</a> · 72 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_ok">Engine.Sync.store_ok</a> ↪ · 31 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onClose_fresh"></a>✅ <a href="../../engine/wire/EgressLaws.lean#L762">Engine.Sync.onClose_fresh</a> · 52 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L194">Engine.Sync.ActsOk.noConn</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_cut_node"></a>✅ <a href="../../app/Proofs.lean#L1151">Connection.rooms_cut_node</a> · 127 below</summary><ul>
<li><details><summary><a id="law-Connection.removal_cuts_off_node"></a>✅ <a href="../../app/connection/Proofs.lean#L608">Connection.removal_cuts_off_node</a> · 118 below</summary><ul>
<li><details><summary><a id="law-Connection.community_inv"></a>✅ <a href="../../app/connection/Family.lean#L632">Connection.community_inv</a> · 81 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.view_node"></a>✅ <a href="../../app/connection/Family.lean#L636">Connection.view_node</a> · 81 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
<li>✅ <a href="#law-Community.removal_cuts_off">Community.removal_cuts_off</a> ↪ · 71 below</li>
<li><details><summary><a id="law-Community.reads_allowPeer"></a>✅ <a href="../../app/connection/Family.lean#L590">Community.reads_allowPeer</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Community.reads_live"></a>✅ <a href="../../app/connection/Family.lean#L576">Community.reads_live</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.reads_deviceLive"></a>✅ <a href="../../app/connection/Family.lean#L569">Community.reads_deviceLive</a> · 3 below</summary><ul>
<li>✅ <a href="../../app/connection/Family.lean#L551">Community.reads_unremoved</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Connection.connect_iff_node">Connection.connect_iff_node</a> ↪ · 115 below</li>
<li>✅ <a href="#law-Connection.rooms_cut">Connection.rooms_cut</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_trusted"></a>✅ <a href="../../app/Proofs.lean#L1109">Connection.rooms_trusted</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.mem_roomsV"></a>✅ <a href="../../app/Proofs.lean#L152">Connection.mem_roomsV</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.eval_roomsOf"></a>▫️ <a href="../../app/Proofs.lean#L143">Connection.eval_roomsOf</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.eval_roomFor"></a>✅ <a href="../../app/Proofs.lean#L127">Connection.eval_roomFor</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_cut"></a>✅ <a href="../../app/Proofs.lean#L1131">Connection.rooms_cut</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Connection.rooms_trusted">Connection.rooms_trusted</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Connection.trusts_live">Connection.trusts_live</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_removed"></a>✅ <a href="../../app/Proofs.lean#L169">Connection.rooms_removed</a> · 6 below</summary><ul>
<li>✅ <a href="#law-Connection.mem_roomsV">Connection.mem_roomsV</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Connection.eval_roomFor">Connection.eval_roomFor</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Connection.trusts_live">Connection.trusts_live</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_complete"></a>✅ <a href="../../app/Proofs.lean#L193">Connection.rooms_complete</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.eval_roomFor">Connection.eval_roomFor</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.eval_roomsOf">Connection.eval_roomsOf</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.notice_then_cut"></a>✅ <a href="../../app/Proofs.lean#L358">Connection.notice_then_cut</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Connection.roomsV_nil"></a>✅ <a href="../../app/Proofs.lean#L253">Connection.roomsV_nil</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Connection.mem_roomsV">Connection.mem_roomsV</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Connection.eval_roomFor">Connection.eval_roomFor</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Connection.trusts_live">Connection.trusts_live</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L174">Connection.has_of_mem</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.openSessions_state">Connection.openSessions_state</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Connection.allSessions_established"></a>▫️ <a href="../../app/Proofs.lean#L345">Connection.allSessions_established</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Connection.mem_sessionsOf"></a>▫️ <a href="../../app/Proofs.lean#L323">Connection.mem_sessionsOf</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L306">Connection.sessionOf_some</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L198">Connection.sessionOf_state</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.allSessions_state">Connection.allSessions_state</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.carrying_mem">Connection.carrying_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.trusts_live"></a>✅ <a href="../../app/Proofs.lean#L112">Connection.trusts_live</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L189">Connection.eval_liftL_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_model"></a>✅ <a href="../../app/Proofs.lean#L1165">Connection.rooms_model</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/View.lean#L55">Engine.View.run_model</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.recv_send">Engine.Sync.recv_send</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.Sync.recv_take"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L129">Engine.Sync.recv_take</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_send">Engine.Sync.onHold_send</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onRbsr_send">Engine.Sync.onRbsr_send</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onWant_send">Engine.Sync.onWant_send</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.start_send">Engine.Sync.start_send</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L107">Engine.Sync.recv_cases</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L38">Engine.Sync.shows_heard</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.removal_reaches_session"></a>✅ <a href="../../app/Proofs.lean#L3104">Connection.removal_reaches_session</a> · 239 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.entry_fresh">Engine.Sync.entry_fresh</a> ↪ · 102 below</li>
<li><details><summary><a id="law-Connection.hooks_readOnly"></a>✅ <a href="../../app/Proofs.lean#L3045">Connection.hooks_readOnly</a> · 89 below</summary><ul>
<li><details><summary><a id="law-Connection.hooks_reads"></a>✅ <a href="../../app/Proofs.lean#L2125">Connection.hooks_reads</a> · 88 below</summary><ul>
<li><details><summary><a id="law-Connection.react_reads"></a>▫️ <a href="../../app/Proofs.lean#L2039">Connection.react_reads</a> · 55 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2017">Connection.answerAll_reads</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Connection.answerOne_reads">Connection.answerOne_reads</a> ↪ · 45 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2035">Connection.establishAll_reads</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.establishReqs_reads">Connection.establishReqs_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L1996">Connection.openAll_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Connection.openEach_reads">Connection.openEach_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.deliverAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2004">Connection.deliverAll_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.joinsOf_reads">Connection.joinsOf_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.endpoints_reads"></a>▫️ <a href="../../app/Proofs.lean#L1972">Connection.endpoints_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L1964">Connection.list_reads</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.onArrival_reads"></a>▫️ <a href="../../app/Proofs.lean#L2114">Connection.onArrival_reads</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.count_reads"></a>▫️ <a href="../../app/Proofs.lean#L1969">Connection.count_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L1964">Connection.list_reads</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.resendConns_reads"></a>▫️ <a href="../../app/Proofs.lean#L2110">Connection.resendConns_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.view_reads"></a>▫️ <a href="../../app/Proofs.lean#L1955">Connection.view_reads</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Proofs.lean#L1949">Connection.view_held</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dial_reads"></a>▫️ <a href="../../app/Proofs.lean#L2066">Connection.dial_reads</a> · 42 below</summary><ul>
<li><details><summary><a id="law-Connection.dialAll_reads"></a>▫️ <a href="../../app/Proofs.lean#L2061">Connection.dialAll_reads</a> · 40 below</summary><ul>
<li>▫️ <a href="#law-Connection.dialOne_reads">Connection.dialOne_reads</a> ↪ · 39 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.endpoints_reads">Connection.endpoints_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L1964">Connection.list_reads</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retired_reads"></a>▫️ <a href="../../app/Proofs.lean#L2100">Connection.retired_reads</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Connection.openSessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2092">Connection.openSessions_reads</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Connection.allSessions_reads">Connection.allSessions_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Connection.carrying_reads">Connection.carrying_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2095">Connection.sessions_reads</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Connection.openSessions_reads">Connection.openSessions_reads</a> ↪ · 12 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.outbox_reads"></a>▫️ <a href="../../app/Proofs.lean#L2107">Connection.outbox_reads</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retryKey_reads"></a>▫️ <a href="../../app/Proofs.lean#L2118">Connection.retryKey_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sealFor_reads"></a>▫️ <a href="../../app/Proofs.lean#L2103">Connection.sealFor_reads</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.keys_reads"></a>▫️ <a href="../../app/Proofs.lean#L1982">Connection.keys_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L55">Connection.sessionKeys_reads</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.closing_reads"></a>▫️ <a href="../../app/Proofs.lean#L2072">Connection.closing_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openFrame_reads"></a>✅ <a href="../../app/connection/Proofs.lean#L76">Connection.openFrame_reads</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.openFrame_run"></a>▫️ <a href="../../app/connection/Proofs.lean#L59">Connection.openFrame_run</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L55">Connection.sessionKeys_reads</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_reads"></a>▫️ <a href="../../app/Proofs.lean#L2075">Connection.rooms_reads</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sent_mayGo"></a>✅ <a href="../../app/Proofs.lean#L3066">Connection.sent_mayGo</a> · 84 below</summary><ul>
<li>✅ <a href="#law-Connection.removed_gets_only_notice">Connection.removed_gets_only_notice</a> ↪ · 41 below</li>
<li><details><summary><a id="law-Engine.Sync.tickGive_held"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L221">Engine.Sync.tickGive_held</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.tickGive_sim"></a>✅ <a href="../../engine/sync/SimLaws.lean#L195">Engine.Sync.tickGive_sim</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.notify_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L152">Engine.Sync.notify_sim</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.give_sim">Engine.Sync.give_sim</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L189">Engine.Sync.tick_sim</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.work_sim">Engine.Sync.work_sim</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L32">Engine.Sync.Sim.run1</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filedGive_held"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L217">Engine.Sync.filedGive_held</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filedGive_sim"></a>✅ <a href="../../engine/sync/SimLaws.lean#L157">Engine.Sync.filedGive_sim</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.notify_sim">Engine.Sync.notify_sim</a> ↪ · 9 below</li>
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
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_shown">Engine.Sync.serveOwed_shown</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.Sync.recv_held"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L212">Engine.Sync.recv_held</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_sim"></a>✅ <a href="../../engine/sync/SimLaws.lean#L201">Engine.Sync.recv_sim</a> · 7 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.sweep_shown"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L309">Engine.Sync.sweep_shown</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sweep_step_shown"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L300">Engine.Sync.sweep_step_shown</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Sweep.next_sent"></a>✅ <a href="../../engine/sync/SweepLaws.lean#L22">Engine.Sync.Sweep.next_sent</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/SweepLaws.lean#L5">Engine.Sync.Sweep.offer_sent</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L305">Engine.Sync.result_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rooms_held"></a>✅ <a href="../../app/Proofs.lean#L1960">Connection.rooms_held</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/Proofs.lean#L1949">Connection.view_held</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.FramesBy.mono"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L678">Engine.Sync.FramesBy.mono</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.notice_sent"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L582">Engine.Sync.notice_sent</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_gives"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L361">Engine.Sync.give_gives</a> · 9 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.closure">Engine.Sync.closure</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.give_given"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L332">Engine.Sync.give_given</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_conn"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L317">Engine.Sync.give_conn</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureOps_state"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L77">Engine.Sync.closureOps_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L45">Engine.Sync.closureOps_nil</a></li>
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
<li><details><summary><a id="law-Engine.Sync.filedGive_run"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L466">Engine.Sync.filedGive_run</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.notify_state"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L463">Engine.Sync.notify_state</a> · 3 below</summary><ul>
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
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L312">Engine.Sync.foldl_inv</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L14">Engine.run_getOp</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tickGive_run"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L473">Engine.Sync.tickGive_run</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.notify_state">Engine.Sync.notify_state</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_given"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L561">Engine.Sync.tick_given</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.walkN_given"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L542">Engine.Sync.walkN_given</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Run.lean#L10">Engine.Model.run_bind</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L14">Engine.run_getOp</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L184">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.give_conn">Engine.Sync.give_conn</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.tick_drop_given"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L497">Engine.Sync.tick_drop_given</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.tick_drop"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L482">Engine.Sync.tick_drop</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L188">Engine.Sync.Step.pulse_drop</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closure"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L284">Engine.Sync.closure</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureOps_complete"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L137">Engine.Sync.closureOps_complete</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closureOps_sound"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L100">Engine.Sync.closureOps_sound</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L45">Engine.Sync.closureOps_nil</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_send"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L613">Engine.Sync.notice_send</a> · 22 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.give_send"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L340">Engine.Sync.give_send</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.closure">Engine.Sync.closure</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.has_of_cons"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L70">Engine.Sync.has_of_cons</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.has_cons_of"></a>▫️ <a href="../../engine/sync/NoticeLaws.lean#L67">Engine.Sync.has_cons_of</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.closureOps_state">Engine.Sync.closureOps_state</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.tick_send">Engine.Sync.tick_send</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.filedGive_run">Engine.Sync.filedGive_run</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.tickGive_run">Engine.Sync.tickGive_run</a> ↪ · 4 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.filed_send">Engine.Sync.filed_send</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.give_conn">Engine.Sync.give_conn</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.removed_gets_only_notice"></a>✅ <a href="../../app/Proofs.lean#L210">Connection.removed_gets_only_notice</a> · 41 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.notice_send">Engine.Sync.notice_send</a> ↪ · 22 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.recv_send">Engine.Sync.recv_send</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Engine.Sync.recv_take">Engine.Sync.recv_take</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Connection.rooms_removed">Connection.rooms_removed</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L427">Engine.Sync.mem_notices</a></li>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_once"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L644">Engine.Sync.notice_once</a> · 15 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.tick_send">Engine.Sync.tick_send</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.filedGive_run">Engine.Sync.filedGive_run</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.tickGive_run">Engine.Sync.tickGive_run</a> ↪ · 4 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.filed_send">Engine.Sync.filed_send</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/sync/NoticeLaws.lean#L408">Engine.Sync.give_quiet</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.notice_no_holds"></a>✅ <a href="../../engine/sync/NoticeLaws.lean#L442">Engine.Sync.notice_no_holds</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/NoticeLaws.lean#L418">Engine.Sync.mem_syncs</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.answer_trusted"></a>✅ <a href="../../app/Proofs.lean#L747">Connection.answer_trusted</a> · 69 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_trusted"></a>▫️ <a href="../../app/Proofs.lean#L675">Connection.answerAll_trusted</a> · 46 below</summary><ul>
<li><details><summary><a id="law-Connection.answerOne_out"></a>▫️ <a href="../../app/Proofs.lean#L487">Connection.answerOne_out</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L271">Connection.run_arrivedFrom</a></li>
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
<li><details><summary><a id="law-Connection.answerOne_state"></a>▫️ <a href="../../app/Proofs.lean#L639">Connection.answerOne_state</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.run_view">Connection.run_view</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L271">Connection.run_arrivedFrom</a></li>
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
<li><details><summary><a id="law-Connection.joinOf_not_conn"></a>▫️ <a href="../../app/Proofs.lean#L730">Connection.joinOf_not_conn</a> · 44 below</summary><ul>
<li><details><summary><a id="law-Connection.joinOf_request"></a>▫️ <a href="../../app/Proofs.lean#L594">Connection.joinOf_request</a> · 40 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
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
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
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
<li><details><summary><a id="law-Connection.establishAll_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L367">Connection.establishAll_body</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Connection.establishReqs_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L350">Connection.establishReqs_body</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Connection.establishConns_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L336">Connection.establishConns_body</a> · 38 below</summary><ul>
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
<li><details><summary><a id="law-Connection.openAll_body"></a>▫️ <a href="../../app/connection/Proofs.lean#L327">Connection.openAll_body</a> · 39 below</summary><ul>
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
<li><details><summary><a id="law-Connection.deliverAll_join"></a>▫️ <a href="../../app/Proofs.lean#L576">Connection.deliverAll_join</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.joinsOf_join"></a>▫️ <a href="../../app/Proofs.lean#L551">Connection.joinsOf_join</a> · 34 below</summary><ul>
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
<li><details><summary><a id="law-Connection.deliverAll_state"></a>▫️ <a href="../../app/Proofs.lean#L717">Connection.deliverAll_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L705">Connection.joinsOf_state</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L321">Connection.openAll_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L314">Connection.openEach_state</a></li>
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
<li><details><summary><a id="law-Connection.resend_trusted"></a>✅ <a href="../../app/Proofs.lean#L793">Connection.resend_trusted</a> · 52 below</summary><ul>
<li><details><summary><a id="law-Connection.receiptFor_receipts"></a>▫️ <a href="../../app/connection/Proofs.lean#L379">Connection.receiptFor_receipts</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L189">Connection.eval_liftL_bind</a></li>
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
<li><details><summary><a id="law-Connection.bare_takes_only_join"></a>✅ <a href="../../app/Proofs.lean#L610">Connection.bare_takes_only_join</a> · 62 below</summary><ul>
<li><details><summary><a id="law-Connection.answerAll_conn"></a>▫️ <a href="../../app/Proofs.lean#L532">Connection.answerAll_conn</a> · 43 below</summary><ul>
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
<li><details><summary><a id="law-Connection.establishAll_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L302">Connection.establishAll_conn</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.establishReqs_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L286">Connection.establishReqs_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L273">Connection.establishConns_conn</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openAll_conn"></a>▫️ <a href="../../app/connection/Proofs.lean#L262">Connection.openAll_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L249">Connection.openEach_conn</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/connection/Proofs.lean#L241">Connection.room_connOp</a></li>
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
<li><a id="law-Engine.intake_local"></a>✅ <a href="../../engine/core/Sync.lean#L44">Engine.intake_local</a></li>
<li><details><summary><a id="law-Engine.stored_local"></a>✅ <a href="../../engine/core/Sync.lean#L114">Engine.stored_local</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.stepS_ops-"></a>▫️ <a href="../../engine/core/Sync.lean#L110">Engine.stepS_ops'</a> · 7 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.foldl_ingest_ops"></a>▫️ <a href="../../engine/core/Sync.lean#L99">Engine.foldl_ingest_ops</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Sync.lean#L89">Engine.ingestS_ops</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L44">Engine.intake_local</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.local_fact_mine"></a>✅ <a href="../../app/community/Family.lean#L1332">Community.local_fact_mine</a> · 59 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>✅ <a href="#law-Engine.stored_local">Engine.stored_local</a> ↪ · 13 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L652">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1322">Community.check_local</a></li>
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
<li><a id="law-Engine.intakeConn_conn"></a>✅ <a href="../../engine/core/Sync.lean#L38">Engine.intakeConn_conn</a></li>
<li><details><summary><a id="law-Connection.established_agrees_sodium"></a>✅ <a href="../../app/Proofs.lean#L98">Connection.established_agrees_sodium</a> · 35 below</summary><ul>
<li>✅ <a href="#law-Connection.established_agrees">Connection.established_agrees</a> ↪ · 30 below</li>
<li>✅ <a href="#law-Connection.Noise.suite_good">Connection.Noise.suite_good</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.established_agrees"></a>✅ <a href="../../app/Proofs.lean#L43">Connection.established_agrees</a> · 30 below</summary><ul>
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
<li><details><summary><a id="law-Connection.sealFor_opens"></a>✅ <a href="../../app/connection/Proofs.lean#L559">Connection.sealFor_opens</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Connection.open_seal_sodium">Connection.open_seal_sodium</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/core/Crypto.lean#L36">Engine.Bytes.of?_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.open_seal_sodium"></a>✅ <a href="../../app/connection/Proofs.lean#L539">Connection.open_seal_sodium</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.open_seal">Connection.open_seal</a> ↪ · 1 below</li>
<li>✅ <a href="../../app/connection/Proofs.lean#L529">Connection.ad_fits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.cid_seal_sodium"></a>✅ <a href="../../app/connection/Proofs.lean#L547">Connection.cid_seal_sodium</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Connection.cid_seal">Connection.cid_seal</a> ↪ · 1 below</li>
<li>✅ <a href="../../app/connection/Proofs.lean#L529">Connection.ad_fits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.open_seal"></a>✅ <a href="../../app/connection/Proofs.lean#L483">Connection.open_seal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L476">Connection.seal_parts</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.cid_seal"></a>✅ <a href="../../app/connection/Proofs.lean#L512">Connection.cid_seal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L476">Connection.seal_parts</a></li>
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
<li><details><summary><a id="law-Engine.Sync.seal_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L549">Engine.Sync.seal_ok</a> · 31 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L424">Engine.Sync.mem_bundles</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.SealedOk.mono"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L543">Engine.Sync.SealedOk.mono</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.open_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L494">Engine.Sync.open_ok</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L203">Engine.Sync.ActsOk.sends</a></li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Goes.bind-"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L63">Engine.Sync.Goes.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L58">Engine.Sync.Reads.goes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.effectsPurge_goes"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L636">Engine.Sync.effectsPurge_goes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.fanout_ok"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L390">Engine.Sync.fanout_ok</a> · 29 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_goes">Engine.Sync.recordGiven_goes</a> ↪ · 13 below</li>
<li><details><summary><a id="law-Engine.Sync.filedGive_reads"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L197">Engine.Sync.filedGive_reads</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filed_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L154">Engine.Sync.filed_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.give_reads">Engine.Sync.give_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
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
<li><details><summary><a id="law-Engine.Sync.sweep_reads"></a>▫️ <a href="../../engine/wire/EgressLaws.lean#L294">Engine.Sync.sweep_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closureOps_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L165">Engine.Sync.closureOps_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Closure.lean#L45">Engine.Sync.closureOps_nil</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.holdsIn_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L158">Engine.Sync.holdsIn_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reads.forIn-"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L133">Engine.Sync.Reads.forIn'</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.forIn_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L95">Engine.Sync.forIn_keeps</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.answerOne_reads"></a>▫️ <a href="../../app/Proofs.lean#L2012">Connection.answerOne_reads</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.arrivedFrom_reads"></a>▫️ <a href="../../app/Proofs.lean#L1975">Connection.arrivedFrom_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 1 below</li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.establishReqs_reads"></a>▫️ <a href="../../app/Proofs.lean#L2030">Connection.establishReqs_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.establishConns_reads"></a>▫️ <a href="../../app/Proofs.lean#L2026">Connection.establishConns_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.rows_reads"></a>▫️ <a href="../../app/Proofs.lean#L1966">Connection.rows_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L1964">Connection.list_reads</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openEach_reads"></a>▫️ <a href="../../app/Proofs.lean#L1992">Connection.openEach_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.joinsOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2000">Connection.joinsOf_reads</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.dialOne_reads"></a>▫️ <a href="../../app/Proofs.lean#L2056">Connection.dialOne_reads</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Connection.requestOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2047">Connection.requestOf_reads</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Connection.helloOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L1987">Connection.helloOf_reads</a> · 32 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.connectedTo_reads"></a>▫️ <a href="../../app/Proofs.lean#L1984">Connection.connectedTo_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.count_reads">Connection.count_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L1964">Connection.list_reads</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.allSessions_reads"></a>▫️ <a href="../../app/Proofs.lean#L2085">Connection.allSessions_reads</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionsOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2081">Connection.sessionsOf_reads</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionOf_reads"></a>▫️ <a href="../../app/Proofs.lean#L2078">Connection.sessionOf_reads</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.arrival_reads"></a>▫️ <a href="../../app/Proofs.lean#L1978">Connection.arrival_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L136">Engine.Sync.Reads.getOp'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.rows_reads">Connection.rows_reads</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.carrying_reads"></a>▫️ <a href="../../app/Proofs.lean#L2088">Connection.carrying_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.view_reads">Connection.view_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.give_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L142">Engine.Sync.give_sim</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureOps_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L120">Engine.Sync.closureOps_sim</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L56">Engine.Sync.Sim.getOp'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L103">Engine.Sync.closureOps_cons</a></li>
<li>▫️ <a href="../../engine/sync/Closure.lean#L45">Engine.Sync.closureOps_nil</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L116">Engine.Sync.closureOps_zero</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.work_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L185">Engine.Sync.work_sim</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.walk_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L181">Engine.Sync.walk_sim</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.walkN_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L161">Engine.Sync.walkN_sim</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L56">Engine.Sync.Sim.getOp'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Sim.bind-"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L38">Engine.Sync.Sim.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Sim.forIn-"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L44">Engine.Sync.Sim.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.holdsIn_sim"></a>▫️ <a href="../../engine/sync/SimLaws.lean#L91">Engine.Sync.holdsIn_sim</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Sim.bind-">Engine.Sync.Sim.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L56">Engine.Sync.Sim.getOp'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L36">Engine.Sync.Sim.pure'</a></li>
</ul></details></li>
</ul>
