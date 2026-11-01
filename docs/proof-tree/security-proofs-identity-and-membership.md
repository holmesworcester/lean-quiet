# Security proofs › Identity and membership

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Security proofs › Identity and membership**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1035) · 🌐 world: the node's code in a World (35) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (319) · 🧪 control: a negative control (24) · ▫️ lemma: not audited (2003)

<ul>
<li><details><summary><a id="law-Community.no_impersonation"></a>✅ <a href="../../app/community/Proofs.lean#L120">Community.no_impersonation</a> · 52 below</summary><ul>
<li>✅ <a href="#law-Community.message_authorized">Community.message_authorized</a> ↪ · 48 below</li>
<li>📐 <a href="#law-Community.admission_consented">Community.admission_consented</a> ↪ · 47 below</li>
<li><details><summary><a id="law-Engine.Codec.decNatFrom_at"></a>▫️ <a href="../../engine/core/Codec.lean#L413">Engine.Codec.decNatFrom_at</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Codec.numEnd_digits_at"></a>▫️ <a href="../../engine/core/Codec.lean#L391">Engine.Codec.numEnd_digits_at</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.Codec.At.cons"></a>▫️ <a href="../../engine/core/Codec.lean#L77">Engine.Codec.At.cons</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L81">Engine.Codec.At.get</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L155">Engine.Codec.encNat_big</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L152">Engine.Codec.encNat_small</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L373">Engine.Codec.numEnd_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L146">Engine.Codec.toNat_big</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L143">Engine.Codec.toNat_small</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Codec.digitsFast_eq"></a>▫️ <a href="../../engine/core/Codec.lean#L338">Engine.Codec.digitsFast_eq</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/Codec.lean#L333">Engine.Codec.digitsFast_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L298">Engine.Codec.digits_add</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L159">Engine.Codec.two_pow_seven</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L382">Engine.Codec.decNatFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Codec.encNatInto_eq"></a>▫️ <a href="../../engine/core/Codec.lean#L264">Engine.Codec.encNatInto_eq</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Codec.contDigitsInto_eq"></a>▫️ <a href="../../engine/core/Codec.lean#L236">Engine.Codec.contDigitsInto_eq</a> · 4 below</summary><ul>
<li>▫️ <a href="../../engine/core/Codec.lean#L221">Engine.Codec.contDigitsLoop_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L206">Engine.Codec.contDigits_add</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L163">Engine.Codec.sub_shift</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L159">Engine.Codec.two_pow_seven</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Codec.encNat_split"></a>▫️ <a href="../../engine/core/Codec.lean#L186">Engine.Codec.encNat_split</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Codec.lean#L155">Engine.Codec.encNat_big</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L155">Engine.Codec.encNat_big</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L152">Engine.Codec.encNat_small</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L163">Engine.Codec.sub_shift</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L159">Engine.Codec.two_pow_seven</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Codec.decLenFrom_at"></a>▫️ <a href="../../engine/core/Codec.lean#L469">Engine.Codec.decLenFrom_at</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.At.cons">Engine.Codec.At.cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L81">Engine.Codec.At.get</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L448">Engine.Codec.decLenFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L461">Engine.Codec.split128</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L146">Engine.Codec.toNat_big</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L143">Engine.Codec.toNat_small</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Codec.decListFrom_at"></a>▫️ <a href="../../engine/core/Codec.lean#L633">Engine.Codec.decListFrom_at</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.At.cons">Engine.Codec.At.cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L81">Engine.Codec.At.get</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Body.decFrom_of"></a>▫️ <a href="../../app/community/Family.lean#L650">Community.Body.decFrom_of</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Codec.At.tag"></a>▫️ <a href="../../engine/core/Codec.lean#L89">Engine.Codec.At.tag</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Codec.lean#L81">Engine.Codec.At.get</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Codec.decBytesL_encBytesL"></a>▫️ <a href="../../engine/core/Codec.lean#L499">Engine.Codec.decBytesL_encBytesL</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
</ul></details></li>
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
<li><details><summary><a id="law-Community.admission_needs_approval"></a>✅ <a href="../../app/community/member/invite/Proofs.lean#L44">Community.admission_needs_approval</a> · 57 below</summary><ul>
<li>✅ <a href="#law-Community.admission_approved">Community.admission_approved</a> ↪ · 46 below</li>
<li>✅ <a href="#law-Community.approval_signed">Community.approval_signed</a> ↪ · 46 below</li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.spec_det"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L112">Engine.spec_det</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_det"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L106">Engine.specAt_det</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_le"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L100">Engine.specAt_le</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_succ"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L82">Engine.specAt_succ</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Community.admission_approved"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L50">Community.admission_approved</a> · 46 below</summary><ul>
<li><details><summary><a id="law-Community.valid_inv"></a>▫️ <a href="../../app/community/Family.lean#L1218">Community.valid_inv</a> · 43 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.spec_valid_inv"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L220">Engine.spec_valid_inv</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L192">Engine.allValid_forall2</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Community.check_admission"></a>▫️ <a href="../../app/community/member/invite/request/approve/admit/Proofs.lean#L6">Community.check_admission</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1195">Community.all2_three</a></li>
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
<li><details><summary><a id="law-Community.request_invited"></a>✅ <a href="../../app/community/member/invite/request/Proofs.lean#L33">Community.request_invited</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_request"></a>▫️ <a href="../../app/community/member/invite/request/Proofs.lean#L7">Community.check_request</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1181">Community.all2_two</a></li>
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
<li><details><summary><a id="law-Community.removal_authorized"></a>✅ <a href="../../app/community/member/Proofs.lean#L50">Community.removal_authorized</a> · 47 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_removal"></a>▫️ <a href="../../app/community/member/Proofs.lean#L10">Community.check_removal</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1190">Community.all2_four</a></li>
<li>▫️ <a href="../../app/community/member/admin/Proofs.lean#L34">Community.isAdmin_sound</a></li>
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
<li><details><summary><a id="law-Community.admin_granted"></a>✅ <a href="../../app/community/member/admin/Proofs.lean#L45">Community.admin_granted</a> · 47 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_admin"></a>▫️ <a href="../../app/community/member/admin/Proofs.lean#L6">Community.check_admin</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1190">Community.all2_four</a></li>
<li>▫️ <a href="../../app/community/member/admin/Proofs.lean#L34">Community.isAdmin_sound</a></li>
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
<li><details><summary><a id="law-Community.removed_stays"></a>✅ <a href="../../app/community/member/remove/Proofs.lean#L28">Community.removed_stays</a> · 6 below</summary><ul>
<li>📐 <a href="quality-proofs-the-engine.md#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.valid_stays"></a>✅ <a href="../../app/community/Family.lean#L1280">Community.valid_stays</a> · 6 below</summary><ul>
<li>📐 <a href="quality-proofs-the-engine.md#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.message_authorized"></a>✅ <a href="../../app/community/channel/message/Proofs.lean#L64">Community.message_authorized</a> · 48 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_child"></a>✅ <a href="../../app/community/channel/message/Proofs.lean#L34">Community.check_child</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.check_message"></a>▫️ <a href="../../app/community/channel/message/Proofs.lean#L9">Community.check_message</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1185">Community.all2_cons2</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1181">Community.all2_two</a></li>
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
<li><details><summary><a id="law-Community.approval_signed"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L35">Community.approval_signed</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_approval"></a>▫️ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L7">Community.check_approval</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1195">Community.all2_three</a></li>
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
<li><details><summary><a id="law-Community.invitation_issued"></a>✅ <a href="../../app/community/member/invite/Proofs.lean#L29">Community.invitation_issued</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_invitation"></a>▫️ <a href="../../app/community/member/invite/Proofs.lean#L9">Community.check_invitation</a> · 26 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1181">Community.all2_two</a></li>
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
<li><details><summary><a id="law-Community.named_by_admin"></a>✅ <a href="../../app/community/Proofs.lean#L183">Community.named_by_admin</a> · 47 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Community.check_named"></a>▫️ <a href="../../app/community/Proofs.lean#L163">Community.check_named</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1185">Community.all2_cons2</a></li>
<li>▫️ <a href="../../app/community/member/admin/Proofs.lean#L34">Community.isAdmin_sound</a></li>
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
<li><details><summary><a id="law-Community.admission_consented"></a>📐 <a href="../../app/community/Proofs.lean#L102">Community.admission_consented</a> · 47 below</summary><ul>
<li>▫️ <a href="#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Community.check_admission">Community.check_admission</a> ↪ · 24 below</li>
<li>▫️ <a href="#law-Community.check_request">Community.check_request</a> ↪ · 24 below</li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Community.admin_removal_stands"></a>✅ <a href="../../app/community/member/Proofs.lean#L64">Community.admin_removal_stands</a> · 49 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.spec_valid_of"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L247">Engine.spec_valid_of</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.specAt_le">Engine.specAt_le</a> ↪ · 5 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L56">Engine.allValid_noInvalid</a></li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L212">Engine.forall2_allValid</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Community.mutual_removal"></a>✅ <a href="../../app/community/member/Proofs.lean#L88">Community.mutual_removal</a> · 50 below</summary><ul>
<li>✅ <a href="#law-Community.admin_removal_stands">Community.admin_removal_stands</a> ↪ · 49 below</li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Community.removed_approver_admits"></a>✅ <a href="../../app/community/member/Proofs.lean#L40">Community.removed_approver_admits</a> · 50 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Community.admit_admits">Community.admit_admits</a> ↪ · 49 below</li>
<li>▫️ <a href="#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.judge_mono"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L68">Engine.judge_mono</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L36">Engine.allValid_mono</a></li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L56">Engine.allValid_noInvalid</a></li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L14">Engine.anyInvalid_mono</a></li>
</ul></details></li>
</ul>
