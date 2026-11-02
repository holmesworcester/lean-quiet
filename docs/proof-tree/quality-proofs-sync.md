# Quality proofs › Sync

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › Sync**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1243) · 🌐 world: the node's code in a World (68) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (285) · 🧪 control: a negative control (32) · ▫️ lemma: not audited (2158)

<ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.terminates"></a>✅ <a href="../../engine/sync/RoundRun.lean#L286">Engine.Sync.RoundRun.terminates</a> · 114 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.next_pending"></a>✅ <a href="../../engine/sync/RoundRun.lean#L204">Engine.Sync.RoundRun.next_pending</a> · 100 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.successor"></a>✅ <a href="../../engine/sync/RoundRun.lean#L199">Engine.Sync.RoundRun.successor</a> · 99 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.conn_returns_claims"></a>✅ <a href="../../engine/sync/RoundRun.lean#L106">Engine.Sync.conn_returns_claims</a> · 98 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.conn_answers_claims"></a>✅ <a href="../../engine/sync/RoundRun.lean#L42">Engine.Sync.conn_answers_claims</a> · 80 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 77 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ofOp_rbsr"></a>▫️ <a href="../../engine/sync/RoundRun.lean#L102">Engine.Sync.ofOp_rbsr</a> · 40 below</summary><ul>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.answer_rank"></a>✅ <a href="../../engine/sync/RoundRun.lean#L241">Engine.Sync.RoundRun.answer_rank</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.piece_misses"></a>✅ <a href="../../engine/sync/RoundRun.lean#L218">Engine.Sync.RoundRun.piece_misses</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.pieces_shrink"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L155">Engine.Sync.pieces_shrink</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.pieces_sub"></a>▫️ <a href="../../engine/sync/Round.lean#L132">Engine.Sync.pieces_sub</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.not_lt">Engine.Sync.Key.not_lt</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Round.lean#L114">Engine.Sync.has_iff</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L97">Engine.Sync.pieces_ends</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.filter_len_lt"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L82">Engine.Sync.filter_len_lt</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L70">Engine.Sync.filter_len_le</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L114">Engine.Sync.has_iff</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L82">Engine.Sync.pick_ne</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L70">Engine.Sync.pick_sub</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L97">Engine.Sync.pieces_ends</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L142">Engine.Sync.runLen_bounds</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.pieces_shrink">Engine.Sync.pieces_shrink</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Sync.filter_len_lt">Engine.Sync.filter_len_lt</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/RoundRun.lean#L267">Engine.Sync.RoundRun.next_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.discovers"></a>✅ <a href="../../engine/sync/RoundRun.lean#L418">Engine.Sync.RoundRun.discovers</a> · 142 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoundRun.next_pending">Engine.Sync.RoundRun.next_pending</a> ↪ · 100 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.wants_seen"></a>✅ <a href="../../engine/sync/RoundRun.lean#L361">Engine.Sync.RoundRun.wants_seen</a> · 87 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.conn_answers_claims">Engine.Sync.conn_answers_claims</a> ↪ · 80 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.admit_covers"></a>✅ <a href="../../engine/sync/RoundRun.lean#L326">Engine.Sync.RoundRun.admit_covers</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.eraseDups_length_le"></a>▫️ <a href="../../engine/sync/ServeLaws.lean#L284">Engine.Sync.eraseDups_length_le</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L275">Engine.Sync.eraseDups_loop_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.chunks_cover"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1146">Engine.Sync.chunks_cover</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1127">Engine.Sync.pieceIds_cover</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.holds_announced"></a>✅ <a href="../../engine/sync/RoundRun.lean#L349">Engine.Sync.RoundRun.holds_announced</a> · 83 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.conn_answers_claims">Engine.Sync.conn_answers_claims</a> ↪ · 80 below</li>
<li>▫️ <a href="#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Tree.answer_step"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L254">Engine.Sync.Tree.answer_step</a> · 63 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.same_of_fp"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L126">Engine.Sync.same_of_fp</a> · 43 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.lbl_inj">Engine.Sync.lbl_inj</a> ↪ · 40 below</li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L292">Engine.Sync.named_sub</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.pieces_shrink">Engine.Sync.pieces_shrink</a> ↪ · 15 below</li>
<li><details><summary><a id="law-Engine.Sync.Tree.pieces_le"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L102">Engine.Sync.Tree.pieces_le</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Tree.pieces_le_aux"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L30">Engine.Sync.Tree.pieces_le_aux</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.lt_asymm">Engine.Sync.Key.lt_asymm</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.Tree.pick_keys_gt"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L23">Engine.Sync.Tree.pick_keys_gt</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Round.lean#L70">Engine.Sync.pick_sub</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L114">Engine.Sync.has_iff</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L97">Engine.Sync.pieces_ends</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.pieces_sub">Engine.Sync.pieces_sub</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L70">Engine.Sync.pick_sub</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.pieces_diff"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L216">Engine.Sync.pieces_diff</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.pieces_sub">Engine.Sync.pieces_sub</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.named_false"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L41">Engine.Sync.named_false</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.pieces_cover"></a>▫️ <a href="../../engine/sync/Round.lean#L120">Engine.Sync.pieces_cover</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Round.lean#L114">Engine.Sync.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.named_symm"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L53">Engine.Sync.named_symm</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L292">Engine.Sync.named_sub</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L70">Engine.Sync.filter_len_le</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L70">Engine.Sync.pick_sub</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.RoundRun.answer_rank">Engine.Sync.RoundRun.answer_rank</a> ↪ · 17 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.diff_of"></a>✅ <a href="../../engine/sync/RoundRun.lean#L390">Engine.Sync.RoundRun.diff_of</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.named_false">Engine.Sync.named_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.has_of_diff"></a>✅ <a href="../../engine/sync/RoundRun.lean#L377">Engine.Sync.RoundRun.has_of_diff</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/RoundRun.lean#L267">Engine.Sync.RoundRun.next_mem</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.live_round_complete"></a>✅ <a href="../../engine/sync/RoundRun.lean#L747">Engine.Sync.live_round_complete</a> · 144 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoundRun.discovers">Engine.Sync.RoundRun.discovers</a> ↪ · 142 below</li>
<li>✅ <a href="#law-Engine.Sync.RoundRun.terminates">Engine.Sync.RoundRun.terminates</a> ↪ · 114 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.quiet_round_log"></a>✅ <a href="../../engine/sync/RoundDepth.lean#L139">Engine.Sync.RoundRun.quiet_round_log</a> · 119 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.quiet_terminates"></a>✅ <a href="../../engine/sync/RoundDepth.lean#L78">Engine.Sync.RoundRun.quiet_terminates</a> · 118 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoundRun.next_pending">Engine.Sync.RoundRun.next_pending</a> ↪ · 100 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.answer_level"></a>✅ <a href="../../engine/sync/RoundDepth.lean#L36">Engine.Sync.RoundRun.answer_level</a> · 20 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.pieces_shrink">Engine.Sync.pieces_shrink</a> ↪ · 15 below</li>
<li>✅ <a href="#law-Engine.Sync.Tree.pieces_le">Engine.Sync.Tree.pieces_le</a> ↪ · 13 below</li>
<li>✅ <a href="../../engine/sync/TreeLaws.lean#L138">Engine.Sync.Tree.runLen_le</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L70">Engine.Sync.filter_len_le</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/RoundRun.lean#L713">Engine.Sync.RoundRun.items_par</a></li>
<li>✅ <a href="../../engine/sync/RoundRun.lean#L267">Engine.Sync.RoundRun.next_mem</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/RoundRun.lean#L713">Engine.Sync.RoundRun.items_par</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.exchange_complete"></a>📐 <a href="../../engine/sync/RoundLaws.lean#L235">Engine.Sync.exchange_complete</a> · 63 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.same_of_fp">Engine.Sync.same_of_fp</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Engine.Sync.pieces_shrink">Engine.Sync.pieces_shrink</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.Sync.pieces_diff">Engine.Sync.pieces_diff</a> ↪ · 13 below</li>
<li><details><summary><a id="law-Engine.Sync.exchange_ids"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L101">Engine.Sync.exchange_ids</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.named_false">Engine.Sync.named_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L59">Engine.Sync.mem_fold</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Sound.symm"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L47">Engine.Sync.Sound.symm</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L295">Engine.Sync.nocol_sub</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.named_symm">Engine.Sync.named_symm</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L70">Engine.Sync.filter_len_le</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L59">Engine.Sync.mem_fold</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L70">Engine.Sync.pick_sub</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Tree.exchange_log"></a>📐 <a href="../../engine/sync/TreeLaws.lean#L213">Engine.Sync.Tree.exchange_log</a> · 71 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.exchange_complete">Engine.Sync.exchange_complete</a> ↪ · 63 below</li>
<li><details><summary><a id="law-Engine.Sync.Tree.exchange_stable"></a>📐 <a href="../../engine/sync/TreeLaws.lean#L175">Engine.Sync.Tree.exchange_stable</a> · 22 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.pieces_shrink">Engine.Sync.pieces_shrink</a> ↪ · 15 below</li>
<li>✅ <a href="#law-Engine.Sync.Tree.pieces_le">Engine.Sync.Tree.pieces_le</a> ↪ · 13 below</li>
<li><details><summary><a id="law-Engine.Sync.Tree.exchange_ids_stable"></a>📐 <a href="../../engine/sync/TreeLaws.lean#L164">Engine.Sync.Tree.exchange_ids_stable</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/sync/TreeLaws.lean#L148">Engine.Sync.Tree.fold_congr</a></li>
</ul></details></li>
<li>📐 <a href="../../engine/sync/TreeLaws.lean#L148">Engine.Sync.Tree.fold_congr</a></li>
<li>✅ <a href="../../engine/sync/TreeLaws.lean#L138">Engine.Sync.Tree.runLen_le</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L70">Engine.Sync.filter_len_le</a></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.Sync.Tree.exchange_ids_stable">Engine.Sync.Tree.exchange_ids_stable</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.conn_runs_exchange"></a>📐 <a href="../../engine/sync/RoundRun.lean#L784">Engine.Sync.conn_runs_exchange</a> · 158 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.live_round_complete">Engine.Sync.live_round_complete</a> ↪ · 144 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.exec_current"></a>📐 <a href="../../engine/sync/RoundRun.lean#L522">Engine.Sync.RoundRun.exec_current</a> · 102 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoundRun.successor">Engine.Sync.RoundRun.successor</a> ↪ · 99 below</li>
<li><details><summary><a id="law-Engine.Sync.conn_round_continues"></a>✅ <a href="../../engine/sync/RoundRun.lean#L79">Engine.Sync.conn_round_continues</a> · 80 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 77 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.advance_empty"></a>📐 <a href="../../engine/sync/RoundRun.lean#L513">Engine.Sync.RoundRun.advance_empty</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.ofOp_rbsr">Engine.Sync.ofOp_rbsr</a> ↪ · 40 below</li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.Sync.exchange_complete">Engine.Sync.exchange_complete</a> ↪ · 63 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.pending_source"></a>📐 <a href="../../engine/sync/RoundRun.lean#L583">Engine.Sync.RoundRun.pending_source</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.asks_have_source"></a>✅ <a href="../../engine/sync/RoundRun.lean#L561">Engine.Sync.RoundRun.asks_have_source</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.mem_inserts"></a>📐 <a href="../../engine/sync/RoundRun.lean#L543">Engine.Sync.RoundRun.mem_inserts</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Sound.symm">Engine.Sync.Sound.symm</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.named_false">Engine.Sync.named_false</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.named_symm">Engine.Sync.named_symm</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/RoundRun.lean#L505">Engine.Sync.RoundRun.exec_runs</a></li>
<li>✅ <a href="../../engine/sync/RoundRun.lean#L713">Engine.Sync.RoundRun.items_par</a></li>
<li>▫️ <a href="../../engine/sync/RoundRun.lean#L720">Engine.Sync.RoundRun.par_alt</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.round_due"></a>✅ <a href="../../engine/sync/EventLaws.lean#L76">Engine.Sync.round_due</a> · 77 below</summary><ul>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.Sync.room_independent">Engine.Sync.room_independent</a> ↪ · 71 below</li>
<li><details><summary><a id="law-Engine.Sync.tick_work"></a>✅ <a href="../../engine/sync/EventLaws.lean#L64">Engine.Sync.tick_work</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L32">Engine.Sync.pulse_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.work_base"></a>✅ <a href="../../engine/sync/EventLaws.lean#L57">Engine.Sync.work_base</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L48">Engine.Sync.retake_fewer</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.shown_due"></a>✅ <a href="../../engine/sync/EventLaws.lean#L108">Engine.Sync.shown_due</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.responder_asks"></a>✅ <a href="../../engine/sync/EventLaws.lean#L123">Engine.Sync.responder_asks</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.tick_work">Engine.Sync.tick_work</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Engine.Sync.work_base">Engine.Sync.work_base</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ask_due"></a>✅ <a href="../../engine/sync/EventLaws.lean#L147">Engine.Sync.ask_due</a> · 47 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.join_round"></a>✅ <a href="../../engine/sync/EventLaws.lean#L272">Engine.Sync.join_round</a> · 104 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.round_due">Engine.Sync.round_due</a> ↪ · 77 below</li>
<li>✅ <a href="#law-Engine.Sync.ask_due">Engine.Sync.ask_due</a> ↪ · 47 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>✅ <a href="#law-Engine.Sync.responder_asks">Engine.Sync.responder_asks</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L668">Engine.Sync.Conn.onAsk_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.no_round_before_safety"></a>✅ <a href="../../engine/sync/EventLaws.lean#L239">Engine.Sync.no_round_before_safety</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.work_no_rbsr"></a>✅ <a href="../../engine/sync/EventLaws.lean#L189">Engine.Sync.work_no_rbsr</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.rbsr_not_chunk"></a>✅ <a href="../../engine/sync/EventLaws.lean#L177">Engine.Sync.rbsr_not_chunk</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L169">Engine.Sync.rbsr_not_hold</a></li>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L173">Engine.Sync.rbsr_not_want</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.work_base">Engine.Sync.work_base</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ask_no_rbsr"></a>✅ <a href="../../engine/sync/EventLaws.lean#L215">Engine.Sync.ask_no_rbsr</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L169">Engine.Sync.rbsr_not_hold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_no_rbsr"></a>✅ <a href="../../engine/sync/EventLaws.lean#L203">Engine.Sync.tick_no_rbsr</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L169">Engine.Sync.rbsr_not_hold</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/EventLaws.lean#L164">Engine.Sync.rbsr_room</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.responder_opens_none"></a>✅ <a href="../../engine/sync/EventLaws.lean#L227">Engine.Sync.responder_opens_none</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.work_no_rbsr">Engine.Sync.work_no_rbsr</a> ↪ · 5 below</li>
<li>✅ <a href="#law-Engine.Sync.ask_no_rbsr">Engine.Sync.ask_no_rbsr</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Engine.Sync.tick_no_rbsr">Engine.Sync.tick_no_rbsr</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.shipped_controls_apply"></a>🧪 <a href="../../engine/sync/EventLaws.lean#L350">Engine.Sync.shipped_controls_apply</a> · 84 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.round_due">Engine.Sync.round_due</a> ↪ · 77 below</li>
<li><details><summary><a id="law-Engine.Sync.shipped_dialer_waits"></a>🧪 <a href="../../engine/sync/EventLaws.lean#L334">Engine.Sync.shipped_dialer_waits</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.rbsr_not_chunk">Engine.Sync.rbsr_not_chunk</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.work_base">Engine.Sync.work_base</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.responder_asks">Engine.Sync.responder_asks</a> ↪ · 4 below</li>
<li>🧪 <a href="../../engine/sync/EventLaws.lean#L320">Engine.Sync.shipped_responder_silent</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.lbl_inj"></a>✅ <a href="../../engine/sync/Fp.lean#L313">Engine.Sync.lbl_inj</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.lbl_eq"></a>▫️ <a href="../../engine/sync/Fp.lean#L269">Engine.Sync.lbl_eq</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.pres_eq"></a>▫️ <a href="../../engine/sync/Fp.lean#L274">Engine.Sync.pres_eq</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.encode_ne_empty"></a>▫️ <a href="../../engine/sync/Fp.lean#L302">Engine.Sync.encode_ne_empty</a> · 25 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L298">Engine.Sync.encNat_ne</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.split_mem"></a>▫️ <a href="../../engine/sync/Fp.lean#L281">Engine.Sync.split_mem</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Key.lt_trichotomy">Engine.Sync.Key.lt_trichotomy</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Codec.encode_inj">Engine.Codec.encode_inj</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L292">Engine.Sync.named_sub</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L295">Engine.Sync.nocol_sub</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.opening_honest"></a>✅ <a href="../../engine/sync/RoundLaws.lean#L324">Engine.Sync.opening_honest</a></li>
<li><details><summary><a id="law-Engine.Sync.num_inj"></a>✅ <a href="../../engine/sync/Fp.lean#L48">Engine.Sync.num_inj</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L43">Engine.Sync.num_pos</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.spec_local"></a>📐 <a href="../../engine/core/Locality.lean#L56">Engine.Sync.spec_local</a> · 8 below</summary><ul>
<li>📐 <a href="quality-proofs-the-engine.md#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.specAt_restrict"></a>▫️ <a href="../../engine/core/Locality.lean#L36">Engine.Sync.specAt_restrict</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Locality.lean#L21">Engine.Sync.Reach.trans</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.conn_answers_ids"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L1578">Engine.Sync.conn_answers_ids</a> · 84 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 77 below</li>
<li>▫️ <a href="#law-Engine.Sync.exchange_ids">Engine.Sync.exchange_ids</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closure_delivered"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L230">Engine.Sync.closure_delivered</a> · 156 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.receives"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L288">Engine.Sync.ReceiverRun.receives</a> · 86 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.invariant"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L260">Engine.Sync.ReceiverRun.invariant</a> · 66 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.store_reachable"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L255">Engine.Sync.ReceiverRun.store_reachable</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_reachable"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L202">Engine.Sync.write_reachable</a> · 7 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.turn_reachable">Engine.Sync.turn_reachable</a> ↪ · 2 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_takes"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L116">Engine.Sync.write_takes</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_preserves_op"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L103">Engine.Sync.write_preserves_op</a> · 14 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L434">Engine.Sync.turn_apply</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.foldl_ingest_new">Engine.Sync.foldl_ingest_new</a> ↪ · 12 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.absentFold_covers"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L87">Engine.Sync.absentFold_covers</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.absentFold_keeps"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L68">Engine.Sync.absentFold_keeps</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/sync/ClosureStore.lean#L48">Engine.Sync.absentStep_keeps</a></li>
</ul></details></li>
<li>📐 <a href="../../engine/sync/ClosureStore.lean#L48">Engine.Sync.absentStep_keeps</a></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L271">Engine.Sync.instLawfulBEqByteArray_engine</a></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.Sync.absentFold_source"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L74">Engine.Sync.absentFold_source</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/sync/ClosureStore.lean#L57">Engine.Sync.absentStep_source</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.absentOf_new">Engine.Sync.absentOf_new</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.store_reachable">Engine.Sync.ReceiverRun.store_reachable</a> ↪ · 8 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L78">Engine.intake_sub</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L86">Engine.mem_intake_shared</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.settled"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L263">Engine.Sync.ReceiverRun.settled</a> · 74 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_settles"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L223">Engine.Sync.write_settles</a> · 68 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.turn_settles">Engine.Sync.turn_settles</a> ↪ · 61 below</li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li>📐 <a href="#law-Engine.Sync.absentFold_source">Engine.Sync.absentFold_source</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.store_reachable">Engine.Sync.ReceiverRun.store_reachable</a> ↪ · 8 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L78">Engine.intake_sub</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.invariant">Engine.Sync.ReceiverRun.invariant</a> ↪ · 66 below</li>
<li>✅ <a href="also-cited.md#law-Engine.Sync.ServiceRun.eventually_emitted">Engine.Sync.ServiceRun.eventually_emitted</a> ↪ · 46 below</li>
<li><details><summary><a id="law-Engine.Sync.finite_eventually_held"></a>📐 <a href="../../engine/sync/ClosureDelivery.lean#L203">Engine.Sync.finite_eventually_held</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.retains"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L279">Engine.Sync.ReceiverRun.retains</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.keeps"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L274">Engine.Sync.ReceiverRun.keeps</a> · 15 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.write_preserves_op">Engine.Sync.write_preserves_op</a> ↪ · 14 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>📐 <a href="#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_offered"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1520">Engine.Sync.stream_offered</a> · 81 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.write_offers_all">Engine.Sync.write_offers_all</a> ↪ · 80 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_delivers"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L868">Engine.Sync.stream_delivers</a> · 134 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.stream_frames"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L799">Engine.Sync.stream_frames</a> · 133 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.op_taken">Engine.Sync.op_taken</a> ↪ · 97 below</li>
<li>🌐 <a href="quality-proofs.md#law-Engine.Sync.want_sends">Engine.Sync.want_sends</a> ↪ · 83 below</li>
<li>🌐 <a href="#law-Engine.Sync.hold_wants">Engine.Sync.hold_wants</a> ↪ · 78 below</li>
<li>🌐 <a href="#law-Engine.Sync.write_offers">Engine.Sync.write_offers</a> ↪ · 65 below</li>
<li><details><summary><a id="law-Engine.Sync.turnH_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L81">Engine.Sync.turnH_one</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.bundles_head"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L492">Engine.Sync.bundles_head</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L467">Engine.Sync.mem_bundles</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L777">Engine.Sync.Who.other_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L785">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L788">Engine.Sync.World.run_peer_other'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L779">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_delivers_steps"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L898">Engine.Sync.stream_delivers_steps</a> · 136 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.stream_delivers">Engine.Sync.stream_delivers</a> ↪ · 134 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L777">Engine.Sync.Who.other_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L794">Engine.Sync.World.run_now</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L785">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L788">Engine.Sync.World.run_peer_other'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L779">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_offered_runs"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1536">Engine.Sync.stream_offered_runs</a> · 89 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.stream_offered">Engine.Sync.stream_offered</a> ↪ · 81 below</li>
<li><details><summary><a id="law-Engine.Sync.World.connect_peer"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L931">Engine.Sync.World.connect_peer</a> · 47 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.connect_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L760">Engine.Sync.connect_run</a> · 44 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L387">Engine.Sync.finish_run</a> · 37 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L366">Engine.Sync.finish_reads</a> · 33 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.sealRetries_reads">Engine.Sync.sealRetries_reads</a> ↪ · 32 below</li>
<li>▫️ <a href="#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 31 below</li>
<li><details><summary><a id="law-Engine.Sync.forIn_fixed"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L106">Engine.Sync.forIn_fixed</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.seal_single"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L336">Engine.Sync.seal_single</a> · 32 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.seal_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L315">Engine.Sync.seal_one</a> · 31 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_fixed">Engine.Sync.forIn_fixed</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Engine.Sync.seal_nil"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L373">Engine.Sync.seal_nil</a> · 28 below</summary><ul>
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
<li>▫️ <a href="../../engine/sync/Notice.lean#L41">Engine.Sync.Room.syncs_sync</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L785">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L779">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L785">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L779">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_delivers_runs"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L945">Engine.Sync.stream_delivers_runs</a> · 184 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.stream_delivers_steps">Engine.Sync.stream_delivers_steps</a> ↪ · 136 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.RoomTree.items_add">Engine.Sync.RoomTree.items_add</a> ↪ · 66 below</li>
<li>▫️ <a href="#law-Engine.Sync.World.connect_peer">Engine.Sync.World.connect_peer</a> ↪ · 47 below</li>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_sends"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L348">Engine.Sync.seal_sends</a> · 32 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.seal_one">Engine.Sync.seal_one</a> ↪ · 31 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.RoomTree.default_items">Engine.Sync.RoomTree.default_items</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_offers"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L572">Engine.Sync.write_offers</a> · 65 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>🌐 <a href="#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li>▫️ <a href="#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li><details><summary><a id="law-Engine.Sync.write_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L284">Engine.Sync.write_one</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.recordGiven_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L290">Engine.Sync.recordGiven_run</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_nil"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L279">Engine.Sync.write_nil</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.refresh_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L275">Engine.Sync.refresh_run</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Notice.lean#L44">Engine.Sync.Room.notices_sync</a></li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L41">Engine.Sync.Room.syncs_sync</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filedGive_quiet"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L246">Engine.Sync.filedGive_quiet</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Notice.lean#L59">Engine.Sync.Step.then_quiet</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.holdsOf_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L461">Engine.Sync.holdsOf_one</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L456">Engine.Sync.chunks_one</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L105">Engine.durable_of_room</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_offers_all"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1428">Engine.Sync.write_offers_all</a> · 80 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_mem"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1394">Engine.Sync.seal_mem</a> · 35 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.cids_fold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1333">Engine.Sync.cids_fold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_fold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1371">Engine.Sync.seal_fold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1352">Engine.Sync.foldl_cons_acc</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1301">Engine.Sync.bundles_cover</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1352">Engine.Sync.foldl_cons_acc</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.fanout_offers"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1281">Engine.Sync.fanout_offers</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filed_offers"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L1235">Engine.Sync.filed_offers</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.holdsOf_cover"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1166">Engine.Sync.holdsOf_cover</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.mem_foldl_ins"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1151">Engine.Sync.mem_foldl_ins</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_fold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1184">Engine.Sync.filed_fold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1263">Engine.Sync.fanout_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_mem"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1093">Engine.Sync.write_mem</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.absent_mem"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1010">Engine.Sync.absent_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L994">Engine.Sync.absent_sub</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1045">Engine.Sync.ingest_get</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1070">Engine.Sync.stored_ids_mem</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L345">Engine.Sync.seal_heat</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L105">Engine.durable_of_room</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.hold_wants"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L589">Engine.Sync.hold_wants</a> · 78 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>🌐 <a href="#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li><details><summary><a id="law-Engine.Sync.plainFrame_body"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L518">Engine.Sync.plainFrame_body</a> · 29 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L511">Engine.Sync.tagged_body</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.plainFrame_head"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L515">Engine.Sync.plainFrame_head</a> · 29 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L503">Engine.Sync.tagged_head</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.lane_want_one"></a>▫️ <a href="../../engine/wire/LaneLaws.lean#L515">Engine.Sync.lane_want_one</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.lane_one"></a>▫️ <a href="../../engine/wire/LaneLaws.lean#L495">Engine.Sync.lane_one</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L490">Engine.Sync.lane_control</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.store_nil"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L299">Engine.Sync.store_nil</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.write_nil">Engine.Sync.write_nil</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.admit_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L53">Engine.Sync.admit_one</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L456">Engine.Sync.chunks_one</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L544">Engine.Sync.split_one</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.op_taken"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L735">Engine.Sync.op_taken</a> · 97 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_hold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L538">Engine.Sync.recv_hold</a> · 51 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.onHold_reads">Engine.Sync.onHold_reads</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.recv_data"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L555">Engine.Sync.recv_data</a> · 45 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOp_data"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L528">Engine.Sync.ofOp_data</a> · 39 below</summary><ul>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 33 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
<li><details><summary><a id="law-Engine.Sync.apply_takes"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L445">Engine.Sync.apply_takes</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.store_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L436">Engine.Sync.store_one</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fanout_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L408">Engine.Sync.fanout_reads</a> · 12 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.filedGive_reads">Engine.Sync.filedGive_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.write_one">Engine.Sync.write_one</a> ↪ · 10 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L424">Engine.Sync.serveOwed_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.apply_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L415">Engine.Sync.apply_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.forIn_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L95">Engine.Sync.forIn_keeps</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.onHold_take"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L548">Engine.Sync.onHold_take</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.successful_fair_extension"></a>🌐 <a href="../../app/Proofs.lean#L1911">Connection.Execution.successful_fair_extension</a> · 9 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.fairRun_fair">Connection.Execution.fairRun_fair</a> ↪ · 6 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L1897">Connection.Execution.prepend_action</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L1888">Connection.Execution.prepend_state</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.fairRun_fair"></a>🌐 <a href="../../app/Proofs.lean#L1841">Connection.Execution.fairRun_fair</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.schedule_queue"></a>▫️ <a href="../../app/Proofs.lean#L1822">Connection.Execution.schedule_queue</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.deliver_queue"></a>▫️ <a href="../../app/Proofs.lean#L1807">Connection.Execution.deliver_queue</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L1802">Connection.Execution.run_queue</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L1802">Connection.Execution.run_queue</a></li>
</ul></details></li>
<li><details><summary><a id="law-Net.FIFO.eventually_delivered"></a>▫️ <a href="../../engine/core/FIFO.lean#L52">Net.FIFO.eventually_delivered</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Net.FIFO.pending_until"></a>▫️ <a href="../../engine/core/FIFO.lean#L40">Net.FIFO.pending_until</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/FIFO.lean#L20">Net.FIFO.pending</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/FIFO.lean#L20">Net.FIFO.pending</a></li>
</ul></details></li>
</ul></details></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.Sync.has_of_mem"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L532">Engine.Sync.has_of_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_store"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L23">Engine.Sync.write_store</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.sealRetries_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L359">Engine.Sync.sealRetries_reads</a> · 32 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L157">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L156">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.seal_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L356">Engine.Sync.seal_reads</a> · 31 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
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
<li><details><summary><a id="law-Engine.Sync.forIn_yield"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L115">Engine.Sync.forIn_yield</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
</ul>
