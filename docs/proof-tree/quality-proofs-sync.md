# Quality proofs › Sync

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › Sync**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1147) · 🌐 world: the node's code in a World (35) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (290) · 🧪 control: a negative control (31) · ▫️ lemma: not audited (2030)

<ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.terminates"></a>✅ <a href="../../engine/sync/RoundRun.lean#L286">Engine.Sync.RoundRun.terminates</a> · 68 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.next_pending"></a>✅ <a href="../../engine/sync/RoundRun.lean#L204">Engine.Sync.RoundRun.next_pending</a> · 48 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.successor"></a>✅ <a href="../../engine/sync/RoundRun.lean#L199">Engine.Sync.RoundRun.successor</a> · 47 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.conn_returns_claims"></a>✅ <a href="../../engine/sync/RoundRun.lean#L106">Engine.Sync.conn_returns_claims</a> · 46 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.conn_answers_claims"></a>✅ <a href="../../engine/sync/RoundRun.lean#L42">Engine.Sync.conn_answers_claims</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.answer_rank"></a>✅ <a href="../../engine/sync/RoundRun.lean#L241">Engine.Sync.RoundRun.answer_rank</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RoundRun.piece_misses"></a>✅ <a href="../../engine/sync/RoundRun.lean#L218">Engine.Sync.RoundRun.piece_misses</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.pieces_shrink"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L155">Engine.Sync.pieces_shrink</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.pieces_sub"></a>▫️ <a href="../../engine/sync/Round.lean#L132">Engine.Sync.pieces_sub</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.not_lt">Engine.Sync.Key.not_lt</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Round.lean#L114">Engine.Sync.has_iff</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L97">Engine.Sync.pieces_ends</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Engine.Sync.RoundRun.discovers"></a>✅ <a href="../../engine/sync/RoundRun.lean#L418">Engine.Sync.RoundRun.discovers</a> · 101 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Tree.answer_step"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L254">Engine.Sync.Tree.answer_step</a> · 63 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.same_of_fp"></a>▫️ <a href="../../engine/sync/RoundLaws.lean#L126">Engine.Sync.same_of_fp</a> · 43 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.lbl_inj">Engine.Sync.lbl_inj</a> ↪ · 40 below</li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L249">Engine.Sync.named_sub</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.pieces_shrink">Engine.Sync.pieces_shrink</a> ↪ · 15 below</li>
<li><details><summary><a id="law-Engine.Sync.Tree.pieces_le"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L102">Engine.Sync.Tree.pieces_le</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Tree.pieces_le_aux"></a>✅ <a href="../../engine/sync/TreeLaws.lean#L30">Engine.Sync.Tree.pieces_le_aux</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_asymm">Engine.Sync.Key.lt_asymm</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
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
<li>▫️ <a href="../../engine/sync/Fp.lean#L249">Engine.Sync.named_sub</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L70">Engine.Sync.filter_len_le</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L38">Engine.Sync.named_iff</a></li>
<li>▫️ <a href="../../engine/sync/Round.lean#L70">Engine.Sync.pick_sub</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.RoundRun.next_pending">Engine.Sync.RoundRun.next_pending</a> ↪ · 48 below</li>
<li>✅ <a href="#law-Engine.Sync.RoundRun.answer_rank">Engine.Sync.RoundRun.answer_rank</a> ↪ · 17 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.wants_seen"></a>✅ <a href="../../engine/sync/RoundRun.lean#L361">Engine.Sync.RoundRun.wants_seen</a> · 11 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.conn_answers_claims">Engine.Sync.conn_answers_claims</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.admit_covers"></a>✅ <a href="../../engine/sync/RoundRun.lean#L326">Engine.Sync.RoundRun.admit_covers</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.eraseDups_length_le"></a>▫️ <a href="../../engine/sync/ServeLaws.lean#L284">Engine.Sync.eraseDups_length_le</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L275">Engine.Sync.eraseDups_loop_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.chunks_cover"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1102">Engine.Sync.chunks_cover</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1083">Engine.Sync.pieceIds_cover</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.holds_announced"></a>✅ <a href="../../engine/sync/RoundRun.lean#L349">Engine.Sync.RoundRun.holds_announced</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.conn_answers_claims">Engine.Sync.conn_answers_claims</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
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
<li><details><summary><a id="law-Engine.Sync.live_round_complete"></a>✅ <a href="../../engine/sync/RoundRun.lean#L747">Engine.Sync.live_round_complete</a> · 103 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoundRun.discovers">Engine.Sync.RoundRun.discovers</a> ↪ · 101 below</li>
<li>✅ <a href="#law-Engine.Sync.RoundRun.terminates">Engine.Sync.RoundRun.terminates</a> ↪ · 68 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
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
<li>▫️ <a href="../../engine/sync/Fp.lean#L252">Engine.Sync.nocol_sub</a></li>
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
<li><details><summary><a id="law-Engine.Sync.conn_runs_exchange"></a>📐 <a href="../../engine/sync/RoundRun.lean#L784">Engine.Sync.conn_runs_exchange</a> · 117 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.live_round_complete">Engine.Sync.live_round_complete</a> ↪ · 103 below</li>
<li>📐 <a href="#law-Engine.Sync.exchange_complete">Engine.Sync.exchange_complete</a> ↪ · 63 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.exec_current"></a>📐 <a href="../../engine/sync/RoundRun.lean#L522">Engine.Sync.RoundRun.exec_current</a> · 50 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoundRun.successor">Engine.Sync.RoundRun.successor</a> ↪ · 47 below</li>
<li><details><summary><a id="law-Engine.Sync.RoundRun.advance_empty"></a>📐 <a href="../../engine/sync/RoundRun.lean#L513">Engine.Sync.RoundRun.advance_empty</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.ofOp_rbsr">Engine.Sync.ofOp_rbsr</a> ↪ · 40 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.conn_round_continues"></a>✅ <a href="../../engine/sync/RoundRun.lean#L79">Engine.Sync.conn_round_continues</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
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
<li><details><summary><a id="law-Engine.Sync.round_due"></a>✅ <a href="../../engine/sync/EventLaws.lean#L76">Engine.Sync.round_due</a> · 8 below</summary><ul>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.Sync.room_independent">Engine.Sync.room_independent</a> ↪ · 2 below</li>
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
<li><details><summary><a id="law-Engine.Sync.join_round"></a>✅ <a href="../../engine/sync/EventLaws.lean#L272">Engine.Sync.join_round</a> · 59 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ask_due">Engine.Sync.ask_due</a> ↪ · 47 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>✅ <a href="#law-Engine.Sync.round_due">Engine.Sync.round_due</a> ↪ · 8 below</li>
<li>✅ <a href="#law-Engine.Sync.responder_asks">Engine.Sync.responder_asks</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L464">Engine.Sync.Conn.onAsk_eq</a></li>
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
<li><details><summary><a id="law-Engine.Sync.shipped_controls_apply"></a>🧪 <a href="../../engine/sync/EventLaws.lean#L350">Engine.Sync.shipped_controls_apply</a> · 15 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.round_due">Engine.Sync.round_due</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.shipped_dialer_waits"></a>🧪 <a href="../../engine/sync/EventLaws.lean#L334">Engine.Sync.shipped_dialer_waits</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.rbsr_not_chunk">Engine.Sync.rbsr_not_chunk</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.work_base">Engine.Sync.work_base</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.responder_asks">Engine.Sync.responder_asks</a> ↪ · 4 below</li>
<li>🧪 <a href="../../engine/sync/EventLaws.lean#L320">Engine.Sync.shipped_responder_silent</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.lbl_inj"></a>✅ <a href="../../engine/sync/Fp.lean#L270">Engine.Sync.lbl_inj</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.lbl_eq"></a>▫️ <a href="../../engine/sync/Fp.lean#L226">Engine.Sync.lbl_eq</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.above_lt"></a>▫️ <a href="../../engine/sync/Fp.lean#L184">Engine.Sync.above_lt</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.below_lt"></a>▫️ <a href="../../engine/sync/Fp.lean#L180">Engine.Sync.below_lt</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L136">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.pres_eq"></a>▫️ <a href="../../engine/sync/Fp.lean#L231">Engine.Sync.pres_eq</a> · 29 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L136">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.encode_ne_empty"></a>▫️ <a href="../../engine/sync/Fp.lean#L259">Engine.Sync.encode_ne_empty</a> · 25 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L255">Engine.Sync.encNat_ne</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.split_mem"></a>▫️ <a href="../../engine/sync/Fp.lean#L238">Engine.Sync.split_mem</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.Key.lt_trichotomy">Engine.Sync.Key.lt_trichotomy</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Codec.encode_inj">Engine.Codec.encode_inj</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L249">Engine.Sync.named_sub</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L252">Engine.Sync.nocol_sub</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L136">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L129">Engine.Sync.top_none</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.opening_honest"></a>✅ <a href="../../engine/sync/RoundLaws.lean#L324">Engine.Sync.opening_honest</a></li>
<li><details><summary><a id="law-Engine.Sync.num_inj"></a>✅ <a href="../../engine/sync/Fp.lean#L40">Engine.Sync.num_inj</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L35">Engine.Sync.num_pos</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.spec_local"></a>📐 <a href="../../engine/core/Locality.lean#L56">Engine.Sync.spec_local</a> · 8 below</summary><ul>
<li>📐 <a href="quality-proofs-the-engine.md#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.specAt_restrict"></a>▫️ <a href="../../engine/core/Locality.lean#L36">Engine.Sync.specAt_restrict</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Locality.lean#L21">Engine.Sync.Reach.trans</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.conn_answers_ids"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L1530">Engine.Sync.conn_answers_ids</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.exchange_ids">Engine.Sync.exchange_ids</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closure_delivered"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L230">Engine.Sync.closure_delivered</a> · 154 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.receives"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L289">Engine.Sync.ReceiverRun.receives</a> · 84 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L297">Engine.Sync.foldl_ingest_keep</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L431">Engine.Sync.turn_apply</a></li>
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
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.settled"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L263">Engine.Sync.ReceiverRun.settled</a> · 73 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_settles"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L223">Engine.Sync.write_settles</a> · 68 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.turn_settles">Engine.Sync.turn_settles</a> ↪ · 61 below</li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li>📐 <a href="#law-Engine.Sync.absentFold_source">Engine.Sync.absentFold_source</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.store_reachable">Engine.Sync.ReceiverRun.store_reachable</a> ↪ · 8 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.invariant">Engine.Sync.ReceiverRun.invariant</a> ↪ · 66 below</li>
<li>✅ <a href="also-cited.md#law-Engine.Sync.ServiceRun.eventually_emitted">Engine.Sync.ServiceRun.eventually_emitted</a> ↪ · 46 below</li>
<li><details><summary><a id="law-Engine.Sync.finite_eventually_held"></a>📐 <a href="../../engine/sync/ClosureDelivery.lean#L203">Engine.Sync.finite_eventually_held</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.retains"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L281">Engine.Sync.ReceiverRun.retains</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.keeps"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L276">Engine.Sync.ReceiverRun.keeps</a> · 15 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.write_preserves_op">Engine.Sync.write_preserves_op</a> ↪ · 14 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>📐 <a href="#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_offered"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1473">Engine.Sync.stream_offered</a> · 82 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.write_offers_all">Engine.Sync.write_offers_all</a> ↪ · 81 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_delivers"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L825">Engine.Sync.stream_delivers</a> · 134 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.stream_frames"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L756">Engine.Sync.stream_frames</a> · 133 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.op_taken">Engine.Sync.op_taken</a> ↪ · 97 below</li>
<li>🌐 <a href="#law-Engine.Sync.want_sends">Engine.Sync.want_sends</a> ↪ · 84 below</li>
<li>🌐 <a href="#law-Engine.Sync.hold_wants">Engine.Sync.hold_wants</a> ↪ · 79 below</li>
<li>🌐 <a href="#law-Engine.Sync.write_offers">Engine.Sync.write_offers</a> ↪ · 66 below</li>
<li><details><summary><a id="law-Engine.Sync.turnH_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L81">Engine.Sync.turnH_one</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.bundles_head"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L449">Engine.Sync.bundles_head</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L424">Engine.Sync.mem_bundles</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L734">Engine.Sync.Who.other_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L742">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L745">Engine.Sync.World.run_peer_other'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L736">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_delivers_steps"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L855">Engine.Sync.stream_delivers_steps</a> · 136 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.stream_delivers">Engine.Sync.stream_delivers</a> ↪ · 134 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L734">Engine.Sync.Who.other_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L751">Engine.Sync.World.run_now</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L742">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L745">Engine.Sync.World.run_peer_other'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L736">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_offered_runs"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1489">Engine.Sync.stream_offered_runs</a> · 90 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.stream_offered">Engine.Sync.stream_offered</a> ↪ · 82 below</li>
<li><details><summary><a id="law-Engine.Sync.World.connect_peer"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L888">Engine.Sync.World.connect_peer</a> · 48 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.connect_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L717">Engine.Sync.connect_run</a> · 45 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L344">Engine.Sync.finish_run</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.finish_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L323">Engine.Sync.finish_reads</a> · 35 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.sealRetries_reads">Engine.Sync.sealRetries_reads</a> ↪ · 34 below</li>
<li>▫️ <a href="#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 33 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Engine.Sync.forIn_fixed"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L106">Engine.Sync.forIn_fixed</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.seal_single"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L293">Engine.Sync.seal_single</a> · 32 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.seal_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L272">Engine.Sync.seal_one</a> · 31 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.seal_nil"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L330">Engine.Sync.seal_nil</a> · 28 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L742">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L736">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L742">Engine.Sync.World.run_peer_other</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L736">Engine.Sync.World.run_peer_self</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.stream_delivers_runs"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L902">Engine.Sync.stream_delivers_runs</a> · 140 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.stream_delivers_steps">Engine.Sync.stream_delivers_steps</a> ↪ · 136 below</li>
<li>▫️ <a href="#law-Engine.Sync.World.connect_peer">Engine.Sync.World.connect_peer</a> ↪ · 48 below</li>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_sends"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L305">Engine.Sync.seal_sends</a> · 32 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.seal_one">Engine.Sync.seal_one</a> ↪ · 31 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_offers"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L529">Engine.Sync.write_offers</a> · 66 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>🌐 <a href="#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li>▫️ <a href="#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li><details><summary><a id="law-Engine.Sync.write_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L241">Engine.Sync.write_one</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.recordGiven_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L247">Engine.Sync.recordGiven_run</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_nil"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L236">Engine.Sync.write_nil</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.refresh_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L232">Engine.Sync.refresh_run</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Notice.lean#L44">Engine.Sync.Room.notices_sync</a></li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L41">Engine.Sync.Room.syncs_sync</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filedGive_quiet"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L203">Engine.Sync.filedGive_quiet</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Notice.lean#L59">Engine.Sync.Step.then_quiet</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.holdsOf_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L418">Engine.Sync.holdsOf_one</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L413">Engine.Sync.chunks_one</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L54">Engine.durable_of_room</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_offers_all"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1384">Engine.Sync.write_offers_all</a> · 81 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_mem"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1350">Engine.Sync.seal_mem</a> · 35 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.cids_fold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1289">Engine.Sync.cids_fold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_fold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1327">Engine.Sync.seal_fold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1308">Engine.Sync.foldl_cons_acc</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1257">Engine.Sync.bundles_cover</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1308">Engine.Sync.foldl_cons_acc</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.fanout_offers"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1237">Engine.Sync.fanout_offers</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.filed_offers"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L1191">Engine.Sync.filed_offers</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.holdsOf_cover"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1122">Engine.Sync.holdsOf_cover</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.mem_foldl_ins"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1107">Engine.Sync.mem_foldl_ins</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_fold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1140">Engine.Sync.filed_fold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1219">Engine.Sync.fanout_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_mem"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1049">Engine.Sync.write_mem</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.absent_mem"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L966">Engine.Sync.absent_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L950">Engine.Sync.absent_sub</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1001">Engine.Sync.ingest_get</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L1026">Engine.Sync.stored_ids_mem</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L302">Engine.Sync.seal_heat</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L54">Engine.durable_of_room</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.hold_wants"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L546">Engine.Sync.hold_wants</a> · 79 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>🌐 <a href="#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li><details><summary><a id="law-Engine.Sync.plainFrame_body"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L475">Engine.Sync.plainFrame_body</a> · 29 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L468">Engine.Sync.tagged_body</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.plainFrame_head"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L472">Engine.Sync.plainFrame_head</a> · 29 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L460">Engine.Sync.tagged_head</a></li>
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
<li><details><summary><a id="law-Engine.Sync.store_nil"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L256">Engine.Sync.store_nil</a> · 2 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L413">Engine.Sync.chunks_one</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L544">Engine.Sync.split_one</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.op_taken"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L692">Engine.Sync.op_taken</a> · 97 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_hold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L495">Engine.Sync.recv_hold</a> · 53 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.onHold_reads">Engine.Sync.onHold_reads</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.recv_data"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L512">Engine.Sync.recv_data</a> · 45 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOp_data"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L485">Engine.Sync.ofOp_data</a> · 39 below</summary><ul>
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
<li>▫️ <a href="#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li><details><summary><a id="law-Engine.Sync.apply_takes"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L402">Engine.Sync.apply_takes</a> · 29 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.store_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L393">Engine.Sync.store_one</a> · 26 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fanout_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L365">Engine.Sync.fanout_reads</a> · 14 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.filedGive_reads">Engine.Sync.filedGive_reads</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.write_one">Engine.Sync.write_one</a> ↪ · 10 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L381">Engine.Sync.serveOwed_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.apply_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L372">Engine.Sync.apply_reads</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_keeps">Engine.Sync.forIn_keeps</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.onHold_take"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L505">Engine.Sync.onHold_take</a> · 1 below</summary><ul>
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
<li><details><summary><a id="law-Connection.Execution.successful_fair_extension"></a>🌐 <a href="../../app/Proofs.lean#L1910">Connection.Execution.successful_fair_extension</a> · 9 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.fairRun_fair">Connection.Execution.fairRun_fair</a> ↪ · 6 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L1896">Connection.Execution.prepend_action</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L1887">Connection.Execution.prepend_state</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.fairRun_fair"></a>🌐 <a href="../../app/Proofs.lean#L1840">Connection.Execution.fairRun_fair</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.schedule_queue"></a>▫️ <a href="../../app/Proofs.lean#L1821">Connection.Execution.schedule_queue</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.deliver_queue"></a>▫️ <a href="../../app/Proofs.lean#L1806">Connection.Execution.deliver_queue</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L1801">Connection.Execution.run_queue</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L1801">Connection.Execution.run_queue</a></li>
</ul></details></li>
<li><details><summary><a id="law-Net.FIFO.eventually_delivered"></a>▫️ <a href="../../engine/core/FIFO.lean#L52">Net.FIFO.eventually_delivered</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Net.FIFO.pending_until"></a>▫️ <a href="../../engine/core/FIFO.lean#L40">Net.FIFO.pending_until</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/FIFO.lean#L20">Net.FIFO.pending</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/FIFO.lean#L20">Net.FIFO.pending</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onWant_all"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L311">Engine.Sync.onWant_all</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L271">Engine.Sync.instLawfulBEqByteArray_engine</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.onWant_order"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L330">Engine.Sync.onWant_order</a></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_head"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L407">Engine.Sync.serveOwed_head</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.serve_head"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L176">Engine.Sync.serve_head</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_fifo"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L414">Engine.Sync.serveOwed_fifo</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_rest"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L157">Engine.Sync.serve_rest</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L32">Engine.Sync.serve_zero</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.owed_within"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L459">Engine.Sync.owed_within</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.owed_drains"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L433">Engine.Sync.owed_drains</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serveOwed_shrinks"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L420">Engine.Sync.serveOwed_shrinks</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_shrinks"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L183">Engine.Sync.serve_shrinks</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.serve_rest">Engine.Sync.serve_rest</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.serveOwed_fifo">Engine.Sync.serveOwed_fifo</a> ↪ · 7 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.want_sends"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L653">Engine.Sync.want_sends</a> · 84 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.ofOp_want">Engine.Sync.ofOp_want</a> ↪ · 39 below</li>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>🌐 <a href="#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_empty"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L335">Engine.Sync.seal_empty</a> · 28 below</summary><ul>
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
<li>▫️ <a href="#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_world"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L622">Engine.Sync.serveOwed_world</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serveOwed_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L589">Engine.Sync.serveOwed_one</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_eq_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L564">Engine.Sync.serveOwed_eq_run</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.fetch_cons">Engine.Sync.fetch_cons</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.hot_single"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L573">Engine.Sync.hot_single</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L561">Engine.Sync.budget_world</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
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
</ul></details></li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.Sync.asks_expire">Engine.Sync.asks_expire</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.write_within"></a>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L220">Engine.Sync.Ingress.Prioritized.write_within</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.write_served"></a>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L205">Engine.Sync.Ingress.Prioritized.write_served</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.write_progress"></a>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L157">Engine.Sync.Ingress.Prioritized.write_progress</a> · 4 below</summary><ul>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L8">Engine.Sync.Inbox.Priority.advance_at_zero</a></li>
<li>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L143">Engine.Sync.Ingress.Prioritized.step_empty_event</a></li>
<li>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L37">Engine.Sync.Ingress.Prioritized.step_event</a></li>
<li>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L30">Engine.Sync.Ingress.Prioritized.step_write</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.source_or_cancelled_within"></a>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L82">Engine.Sync.Ingress.Prioritized.source_or_cancelled_within</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.served_or_cancelled"></a>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L56">Engine.Sync.Ingress.Prioritized.served_or_cancelled</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.step_progress"></a>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L65">Engine.Sync.Ingress.Prioritized.step_progress</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.poll_exists"></a>✅ <a href="../../engine/wire/IngressPriorityLaws.lean#L56">Engine.Sync.Ingress.Prioritized.poll_exists</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.scan_ready"></a>📐 <a href="../../engine/wire/IngressLaws.lean#L30">Engine.Sync.Ingress.scan_ready</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/wire/IngressLaws.lean#L19">Engine.Sync.Ingress.advance_distance</a></li>
</ul></details></li>
<li>📐 <a href="../../engine/wire/IngressLaws.lean#L5">Engine.Sync.Ingress.distance_lt</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.poll_progress"></a>📐 <a href="../../engine/wire/IngressLaws.lean#L94">Engine.Sync.Ingress.poll_progress</a> · 3 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.Ingress.scan_ready">Engine.Sync.Ingress.scan_ready</a> ↪ · 1 below</li>
<li>📐 <a href="../../engine/wire/IngressLaws.lean#L5">Engine.Sync.Ingress.distance_lt</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.step_only_event"></a>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L46">Engine.Sync.Ingress.Prioritized.step_only_event</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L37">Engine.Sync.Ingress.Prioritized.step_event</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L11">Engine.Sync.Inbox.Priority.advance_positive</a></li>
<li>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L37">Engine.Sync.Ingress.Prioritized.step_event</a></li>
<li>📐 <a href="../../engine/wire/IngressPriorityLaws.lean#L30">Engine.Sync.Ingress.Prioritized.step_write</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.changes_preserve"></a>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L35">Engine.Sync.Ingress.Prioritized.changes_preserve</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.arrivals_preserve"></a>📐 <a href="../../engine/wire/IngressLaws.lean#L121">Engine.Sync.Ingress.arrivals_preserve</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/IngressLaws.lean#L77">Engine.Sync.Ingress.offer_preserves</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.cancelAll_preserves"></a>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L15">Engine.Sync.Ingress.cancelAll_preserves</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/IngressChurnLaws.lean#L9">Engine.Sync.Ingress.cancel_other</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="../../engine/wire/IngressLaws.lean#L5">Engine.Sync.Ingress.distance_lt</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.write_within_churn"></a>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L116">Engine.Sync.Ingress.Prioritized.write_within_churn</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.write_served_churn"></a>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L100">Engine.Sync.Ingress.Prioritized.write_served_churn</a> · 6 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.Ingress.Prioritized.write_progress">Engine.Sync.Ingress.Prioritized.write_progress</a> ↪ · 4 below</li>
<li>📐 <a href="../../engine/wire/IngressChurnLaws.lean#L93">Engine.Sync.Ingress.Prioritized.Waiting.same_inputs</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Inbox.Priority.write_within"></a>📐 <a href="../../engine/wire/PriorityLaws.lean#L167">Engine.Sync.Inbox.Priority.write_within</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Inbox.Priority.served"></a>📐 <a href="../../engine/wire/PriorityLaws.lean#L150">Engine.Sync.Inbox.Priority.served</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Inbox.Priority.waiting_step"></a>📐 <a href="../../engine/wire/PriorityLaws.lean#L63">Engine.Sync.Inbox.Priority.waiting_step</a> · 6 below</summary><ul>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L8">Engine.Sync.Inbox.Priority.advance_at_zero</a></li>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L11">Engine.Sync.Inbox.Priority.advance_positive</a></li>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L39">Engine.Sync.Inbox.Priority.step_event</a></li>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L50">Engine.Sync.Inbox.Priority.step_only_event</a></li>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L45">Engine.Sync.Inbox.Priority.step_only_write</a></li>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L33">Engine.Sync.Inbox.Priority.step_write</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Inbox.Priority.event_within"></a>📐 <a href="../../engine/wire/PriorityLaws.lean#L175">Engine.Sync.Inbox.Priority.event_within</a> · 8 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.Inbox.Priority.served">Engine.Sync.Inbox.Priority.served</a> ↪ · 7 below</li>
</ul></details></li>
<li><a id="law-Engine.Sync.Inbox.Priority.local_share"></a>📐 <a href="../../engine/wire/PriorityLaws.lean#L28">Engine.Sync.Inbox.Priority.local_share</a></li>
<li><a id="law-Engine.Sync.Inbox.Priority.phase_cycle"></a>📐 <a href="../../engine/wire/PriorityLaws.lean#L22">Engine.Sync.Inbox.Priority.phase_cycle</a></li>
<li><details><summary><a id="law-Engine.Sync.Loop.turn_records"></a>✅ <a href="../../engine/wire/LoopLaws.lean#L89">Engine.Sync.Loop.turn_records</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/wire/LoopLaws.lean#L39">Engine.Sync.Loop.dispatch_records</a></li>
<li>▫️ <a href="../../engine/wire/LoopLaws.lean#L82">Engine.Sync.Loop.inbox_phase</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Loop.turn_timer"></a>✅ <a href="../../engine/wire/LoopLaws.lean#L103">Engine.Sync.Loop.turn_timer</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/wire/LoopLaws.lean#L39">Engine.Sync.Loop.dispatch_records</a></li>
<li>✅ <a href="../../engine/wire/LoopLaws.lean#L59">Engine.Sync.Loop.dispatch_timer</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Tick.cofinal"></a>✅ <a href="../../engine/wire/LaneLaws.lean#L445">Engine.Sync.Tick.cofinal</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L430">Engine.Sync.Tick.due</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.urgent_ahead"></a>📐 <a href="../../engine/wire/LaneLaws.lean#L108">Engine.Sync.urgent_ahead</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L91">Engine.Sync.pushAll_lanes</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L76">Engine.Sync.take_urgent_first</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ahead_bytes"></a>📐 <a href="../../engine/wire/LaneLaws.lean#L179">Engine.Sync.ahead_bytes</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.lanes_bounded"></a>📐 <a href="../../engine/wire/LaneLaws.lean#L164">Engine.Sync.lanes_bounded</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.take_bytes"></a>📐 <a href="../../engine/wire/LaneLaws.lean#L145">Engine.Sync.take_bytes</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.take_append"></a>📐 <a href="../../engine/wire/LaneLaws.lean#L81">Engine.Sync.take_append</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.cut_append"></a>▫️ <a href="../../engine/wire/LaneLaws.lean#L55">Engine.Sync.cut_append</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L34">Engine.Sync.fill_append</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L116">Engine.Sync.bytesOf_append</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L130">Engine.Sync.push_capped</a></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.Sync.take_bytes">Engine.Sync.take_bytes</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.pushAll_bytes"></a>▫️ <a href="../../engine/wire/LaneLaws.lean#L121">Engine.Sync.pushAll_bytes</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L116">Engine.Sync.bytesOf_append</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L91">Engine.Sync.pushAll_lanes</a></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.Sync.take_append">Engine.Sync.take_append</a> ↪ · 2 below</li>
<li>📐 <a href="#law-Engine.Sync.urgent_ahead">Engine.Sync.urgent_ahead</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.cut_bytes">Engine.Sync.cut_bytes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L116">Engine.Sync.bytesOf_append</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L91">Engine.Sync.pushAll_lanes</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L76">Engine.Sync.take_urgent_first</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.cut_bytes"></a>✅ <a href="../../engine/wire/LaneLaws.lean#L61">Engine.Sync.cut_bytes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L43">Engine.Sync.fill_bytes</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.push_capped"></a>✅ <a href="../../engine/wire/LaneLaws.lean#L130">Engine.Sync.push_capped</a></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_hot"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L389">Engine.Sync.serveOwed_hot</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fetch_all"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L236">Engine.Sync.fetch_all</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.fetch_cons">Engine.Sync.fetch_cons</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li><a id="law-Engine.Sync.hot_ids"></a>✅ <a href="../../engine/wire/LaneLaws.lean#L500">Engine.Sync.hot_ids</a></li>
<li><a id="law-Engine.Sync.lane_control"></a>✅ <a href="../../engine/wire/LaneLaws.lean#L490">Engine.Sync.lane_control</a></li>
<li><details><summary><a id="law-Engine.Sync.fresh_served"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L640">Engine.Sync.fresh_served</a> · 15 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.serveOwed_world">Engine.Sync.serveOwed_world</a> ↪ · 13 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L500">Engine.Sync.hot_ids</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_hot"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1456">Engine.Sync.write_hot</a> · 56 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li><details><summary><a id="law-Engine.Sync.store_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1445">Engine.Sync.store_keeps</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fanout_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1437">Engine.Sync.fanout_keeps</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1418">Engine.Sync.write_keeps</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L506">Engine.Sync.heat_hot</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.onWrite_receives"></a>🌐 <a href="../../app/Proofs.lean#L3201">Connection.Execution.onWrite_receives</a> · 108 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.store_receives"></a>🌐 <a href="../../app/Proofs.lean#L3181">Connection.Execution.store_receives</a> · 70 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.write_receives"></a>🌐 <a href="../../app/Proofs.lean#L3159">Connection.Execution.write_receives</a> · 38 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.write_takes">Engine.Sync.write_takes</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Connection.Execution.write_store_tape"></a>📐 <a href="../../app/Proofs.lean#L3134">Connection.Execution.write_store_tape</a> · 7 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.Execution.M.forIn_reads"></a>▫️ <a href="../../app/Proofs.lean#L3125">Connection.Execution.M.forIn_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L2146">Connection.Execution.M.bind_apply</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2146">Connection.Execution.M.bind_apply</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L3122">Connection.Execution.M.getOp_apply</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.fanout_goes"></a>▫️ <a href="../../app/Proofs.lean#L2798">Connection.Execution.NodeTape.fanout_goes</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.recordGiven_goes"></a>▫️ <a href="../../app/Proofs.lean#L2792">Connection.Execution.NodeTape.recordGiven_goes</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.put_goes"></a>▫️ <a href="../../app/Proofs.lean#L2790">Connection.Execution.NodeTape.put_goes</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.write_goes">Connection.Execution.NodeTape.write_goes</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.GoesM.bind-"></a>▫️ <a href="../../app/Proofs.lean#L2650">Connection.Execution.GoesM.bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.filedGive_reads"></a>▫️ <a href="../../app/Proofs.lean#L2772">Connection.Execution.NodeTape.filedGive_reads</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.give_reads"></a>▫️ <a href="../../app/Proofs.lean#L2764">Connection.Execution.NodeTape.give_reads</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.closure_reads">Connection.Execution.NodeTape.closure_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2155">Connection.Execution.ReadsHeld.bind'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2154">Connection.Execution.ReadsHeld.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.filed_reads"></a>▫️ <a href="../../app/Proofs.lean#L2741">Connection.Execution.NodeTape.filed_reads</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.forIn-">Connection.Execution.ReadsHeld.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2155">Connection.Execution.ReadsHeld.bind'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2170">Connection.Execution.ReadsHeld.getOp'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2154">Connection.Execution.ReadsHeld.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2155">Connection.Execution.ReadsHeld.bind'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2154">Connection.Execution.ReadsHeld.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.GoesM.forIn-"></a>▫️ <a href="../../app/Proofs.lean#L2653">Connection.Execution.GoesM.forIn'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.refresh_reads"></a>▫️ <a href="../../app/Proofs.lean#L2796">Connection.Execution.NodeTape.refresh_reads</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L2155">Connection.Execution.ReadsHeld.bind'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2154">Connection.Execution.ReadsHeld.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.ReadsHeld.goes"></a>▫️ <a href="../../app/Proofs.lean#L2645">Connection.Execution.ReadsHeld.goes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L53">Engine.Sync.Moves.of_eq</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.committed_bind"></a>✅ <a href="../../app/Proofs.lean#L3174">Connection.Execution.committed_bind</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Moves.shared_retained"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L122">Engine.Sync.Moves.shared_retained</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.purge_shared">Engine.purge_shared</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L297">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.put_goes">Connection.Execution.NodeTape.put_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L54">Engine.durable_of_room</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.finish_goes"></a>▫️ <a href="../../app/Proofs.lean#L2823">Connection.Execution.NodeTape.finish_goes</a> · 43 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.sealRetries_goes"></a>▫️ <a href="../../app/Proofs.lean#L2818">Connection.Execution.NodeTape.sealRetries_goes</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.seal_goes"></a>▫️ <a href="../../app/Proofs.lean#L2816">Connection.Execution.NodeTape.seal_goes</a> · 34 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
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
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.seal_goes">Connection.Execution.NodeTape.seal_goes</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.endSession_goes"></a>▫️ <a href="../../app/Proofs.lean#L2821">Connection.Execution.NodeTape.endSession_goes</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.effectsPurge_goes"></a>▫️ <a href="../../app/Proofs.lean#L2812">Connection.Execution.NodeTape.effectsPurge_goes</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.purge-"></a>▫️ <a href="../../app/Proofs.lean#L2671">Connection.Execution.GoesM.purge'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.flush_goes"></a>▫️ <a href="../../app/Proofs.lean#L2814">Connection.Execution.NodeTape.flush_goes</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.NodeTape.effectsPurge_goes">Connection.Execution.NodeTape.effectsPurge_goes</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.follow_goes"></a>▫️ <a href="../../app/Proofs.lean#L2809">Connection.Execution.NodeTape.follow_goes</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.NodeTape.open_goes"></a>▫️ <a href="../../app/Proofs.lean#L2806">Connection.Execution.NodeTape.open_goes</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li>✅ <a href="#law-Connection.Execution.committed_bind">Connection.Execution.committed_bind</a> ↪ · 13 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.converge"></a>🌐 <a href="../../engine/world/Plain.lean#L203">Engine.World.Plain.converge</a> · 130 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.grows">Engine.World.Plain.grows</a> ↪ · 121 below</li>
<li><details><summary><a id="law-Engine.World.converge_of_edge"></a>▫️ <a href="../../engine/world/Epidemic.lean#L209">Engine.World.converge_of_edge</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.World.within_of"></a>▫️ <a href="../../engine/world/Epidemic.lean#L196">Engine.World.within_of</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.World.hops"></a>▫️ <a href="../../engine/world/Epidemic.lean#L73">Engine.World.hops</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Exec.now_mono"></a>▫️ <a href="../../engine/world/Epidemic.lean#L52">Engine.World.Exec.now_mono</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L32">Engine.World.step_now</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Net.Calm.mono"></a>▫️ <a href="../../engine/world/Epidemic.lean#L65">Engine.World.Net.Calm.mono</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L62">Engine.World.Net.Live.mono</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L62">Engine.World.Net.Live.mono</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Net.Calm.mono">Engine.World.Net.Calm.mono</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L93">Engine.World.held_on</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.offline"></a>🌐 <a href="../../engine/world/Plain.lean#L215">Engine.World.Plain.offline</a> · 132 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.grows">Engine.World.Plain.grows</a> ↪ · 121 below</li>
<li><details><summary><a id="law-Engine.World.offline_of"></a>▫️ <a href="../../engine/world/Epidemic.lean#L269">Engine.World.offline_of</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.converge_of_edge">Engine.World.converge_of_edge</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L165">Engine.World.fin_max</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.grows"></a>🌐 <a href="../../engine/world/Plain.lean#L193">Engine.World.Plain.grows</a> · 121 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.step_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L144">Engine.World.Plain.step_keeps</a> · 120 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.enter_moves"></a>▫️ <a href="../../engine/world/Plain.lean#L122">Engine.World.Plain.enter_moves</a> · 99 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.entry_fresh">Engine.Sync.entry_fresh</a> ↪ · 96 below</li>
<li><details><summary><a id="law-Engine.World.Plain.connect_moves"></a>▫️ <a href="../../engine/world/Plain.lean#L112">Engine.World.Plain.connect_moves</a> · 53 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.finish_ok">Engine.Sync.finish_ok</a> ↪ · 51 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.open_ok">Engine.Sync.open_ok</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L44">Engine.Sync.Moves.trans</a></li>
<li>▫️ <a href="../../engine/world/Plain.lean#L95">Engine.World.Plain.plain_readOnly</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Plain.lean#L95">Engine.World.Plain.plain_readOnly</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.enter_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L134">Engine.World.Plain.enter_keeps</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.World.moves_keep"></a>▫️ <a href="../../engine/world/Plain.lean#L83">Engine.World.moves_keep</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.World.move_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L77">Engine.World.move_keeps</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.turn_keeps">Engine.World.turn_keeps</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Engine.World.purge_keeps">Engine.World.purge_keeps</a> ↪ · 9 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Plain.lean#L33">Engine.World.KeepsRooms.refl</a></li>
<li>▫️ <a href="../../engine/world/Plain.lean#L35">Engine.World.KeepsRooms.trans</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Plain.lean#L33">Engine.World.KeepsRooms.refl</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Plain.lean#L33">Engine.World.KeepsRooms.refl</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.managed_nil"></a>🌐 <a href="../../engine/world/Inv.lean#L150">Engine.World.Plain.managed_nil</a> · 78 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onFrame_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L97">Engine.World.onFrame_managed</a> · 68 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onSealed_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L80">Engine.World.onSealed_managed</a> · 65 below</summary><ul>
<li><details><summary><a id="law-Engine.World.finish_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L52">Engine.World.finish_managed</a> · 39 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.apply_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L37">Engine.World.apply_managed</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L424">Engine.World.store_facts</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.fanout_asked">Engine.World.fanout_asked</a> ↪ · 18 below</li>
<li>▫️ <a href="#law-Engine.World.fanout_facts">Engine.World.fanout_facts</a> ↪ · 16 below</li>
<li>▫️ <a href="#law-Engine.World.write_addrs">Engine.World.write_addrs</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.write_keeps">Engine.Sync.write_keeps</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L31">Engine.World.drop_managed</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L17">Engine.World.serveOwed_managed</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.finish_managed">Engine.World.finish_managed</a> ↪ · 39 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_keeps">Engine.Sync.store_keeps</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.Sync.write_keeps">Engine.Sync.write_keeps</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onTick_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L112">Engine.World.onTick_managed</a> · 68 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_managed">Engine.World.finish_managed</a> ↪ · 39 below</li>
<li>▫️ <a href="#law-Engine.World.apply_managed">Engine.World.apply_managed</a> ↪ · 27 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_keeps">Engine.Sync.store_keeps</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L17">Engine.World.serveOwed_managed</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L27">Engine.World.sweep_none</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onWrite_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L56">Engine.World.onWrite_managed</a> · 56 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_managed">Engine.World.finish_managed</a> ↪ · 39 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_keeps">Engine.Sync.store_keeps</a> ↪ · 19 below</li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onClose_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L62">Engine.World.onClose_managed</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_managed">Engine.World.finish_managed</a> ↪ · 39 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L31">Engine.World.drop_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.connect_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L73">Engine.World.connect_managed</a> · 40 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_managed">Engine.World.finish_managed</a> ↪ · 39 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.owes_queued_start"></a>🌐 <a href="../../engine/world/InvIx.lean#L704">Engine.World.Plain.owes_queued_start</a> · 116 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.owes_queued"></a>▫️ <a href="../../engine/world/InvIx.lean#L678">Engine.World.Plain.owes_queued</a> · 115 below</summary><ul>
<li><details><summary><a id="law-Engine.World.oq_pieces"></a>▫️ <a href="../../engine/world/InvIx.lean#L404">Engine.World.oq_pieces</a> · 67 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L379">Engine.World.store_oq</a> · 26 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L198">Engine.World.SameQ.oq</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.World.recv_owed">Engine.World.recv_owed</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.World.serve_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L387">Engine.World.serve_oq</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.World.serveOwed_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L326">Engine.World.serveOwed_oq</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.serve_rest">Engine.Sync.serve_rest</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_erase_mem">Engine.World.foldl_erase_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.oq_replace"></a>▫️ <a href="../../engine/world/InvIx.lean#L222">Engine.World.oq_replace</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvIx.lean#L206">Engine.World.oq_map</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L398">Engine.World.finish_oq</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.World.finish_node"></a>▫️ <a href="../../engine/world/InvIx.lean#L72">Engine.World.finish_node</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.oq_drop"></a>▫️ <a href="../../engine/world/InvIx.lean#L257">Engine.World.oq_drop</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.oq_sent"></a>▫️ <a href="../../engine/world/InvIx.lean#L260">Engine.World.oq_sent</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvIx.lean#L206">Engine.World.oq_map</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L201">Engine.World.oq_conns</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.tickGive_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L298">Engine.World.tickGive_q</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.World.tick_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L275">Engine.World.tick_q</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.ask_q">Engine.World.ask_q</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.start_q">Engine.World.start_q</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L281">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L287">Engine.World.give_q</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.apply_gen"></a>▫️ <a href="../../engine/world/InvIx.lean#L359">Engine.World.apply_gen</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.oq_drop">Engine.World.oq_drop</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.oq_replace">Engine.World.oq_replace</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L41">Engine.Sync.Room.syncs_sync</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L198">Engine.World.SameQ.oq</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L201">Engine.World.oq_conns</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.always"></a>▫️ <a href="../../engine/world/InvIx.lean#L628">Engine.World.Plain.always</a> · 56 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onFrame_keeps"></a>▫️ <a href="../../engine/world/InvIx.lean#L120">Engine.World.onFrame_keeps</a> · 42 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onSealed_keeps"></a>▫️ <a href="../../engine/world/InvIx.lean#L99">Engine.World.onSealed_keeps</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Engine.World.onTick_keeps"></a>▫️ <a href="../../engine/world/InvIx.lean#L136">Engine.World.onTick_keeps</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.tickGive_reads">Engine.Sync.tickGive_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L27">Engine.World.sweep_none</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L181">Engine.World.connect_keeps</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L170">Engine.World.onClose_keeps</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L164">Engine.World.onWrite_keeps</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.ix_covers_start"></a>🌐 <a href="../../engine/world/InvIx.lean#L697">Engine.World.Plain.ix_covers_start</a> · 113 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.ix_covers"></a>▫️ <a href="../../engine/world/InvIx.lean#L689">Engine.World.Plain.ix_covers</a> · 112 below</summary><ul>
<li><details><summary><a id="law-Engine.World.ix_pieces"></a>▫️ <a href="../../engine/world/InvIx.lean#L599">Engine.World.ix_pieces</a> · 94 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L574">Engine.World.store_ixinv</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L510">Engine.World.write_ixinv</a> · 29 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.covers_foldl">Engine.World.covers_foldl</a> ↪ · 13 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_ingestS_isSome">Engine.World.foldl_ingestS_isSome</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L423">Engine.Sync.foldl_fileStep</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L473">Engine.World.foldl_ingestS_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_ix"></a>▫️ <a href="../../engine/world/Owed.lean#L128">Engine.World.fanout_ix</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.fanout_reads">Engine.Sync.fanout_reads</a> ↪ · 14 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L452">Engine.World.ixinv_of_ix</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li>▫️ <a href="#law-Engine.World.write_ixinv">Engine.World.write_ixinv</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.World.apply_gen">Engine.World.apply_gen</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.World.serveOwed_ix"></a>▫️ <a href="../../engine/world/InvIx.lean#L586">Engine.World.serveOwed_ix</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.finish_node">Engine.World.finish_node</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L452">Engine.World.ixinv_of_ix</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Plain.always">Engine.World.Plain.always</a> ↪ · 56 below</li>
<li><details><summary><a id="law-Engine.World.boot_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L563">Engine.World.boot_ixinv</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.covers_foldl">Engine.World.covers_foldl</a> ↪ · 13 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 4 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_wants"></a>🌐 <a href="../../engine/world/Link.lean#L99">Engine.World.Plain.deliver_wants</a> · 165 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_wants">Engine.World.onSealed_wants</a> ↪ · 155 below</li>
<li><details><summary><a id="law-Engine.World.Plain.onFrame_plain"></a>▫️ <a href="../../engine/world/Link.lean#L75">Engine.World.Plain.onFrame_plain</a> · 33 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
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
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_box"></a>▫️ <a href="../../engine/world/Link.lean#L50">Engine.World.Plain.deliver_box</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_sends"></a>▫️ <a href="../../engine/world/Link.lean#L65">Engine.World.Plain.deliver_sends</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Link.lean#L23">Engine.World.mem_packets</a></li>
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
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_queues"></a>🌐 <a href="../../engine/world/Link.lean#L120">Engine.World.Plain.deliver_queues</a> · 176 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_queues">Engine.World.onSealed_queues</a> ↪ · 166 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.onFrame_plain">Engine.World.Plain.onFrame_plain</a> ↪ · 33 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_node"></a>▫️ <a href="../../engine/world/Link.lean#L57">Engine.World.Plain.deliver_node</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Plain.deliver_sends">Engine.World.Plain.deliver_sends</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Engine.World.Plain.deliver_takes"></a>🌐 <a href="../../engine/world/Link.lean#L83">Engine.World.Plain.deliver_takes</a> · 121 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onFrame_takes"></a>▫️ <a href="../../engine/world/Hops.lean#L400">Engine.World.onFrame_takes</a> · 118 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_takes">Engine.World.onSealed_takes</a> ↪ · 113 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
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
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Plain.deliver_box">Engine.World.Plain.deliver_box</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_wants"></a>🌐 <a href="../../engine/world/Asks.lean#L596">Engine.World.onSealed_wants</a> · 155 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recv_hold">Engine.Sync.recv_hold</a> ↪ · 53 below</li>
<li><details><summary><a id="law-Engine.World.payload_run"></a>▫️ <a href="../../engine/world/Hops.lean#L284">Engine.World.payload_run</a> · 49 below</summary><ul>
<li><details><summary><a id="law-Engine.World.apply_store"></a>▫️ <a href="../../engine/world/Hops.lean#L248">Engine.World.apply_store</a> · 40 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.store_one">Engine.Sync.store_one</a> ↪ · 26 below</li>
<li><details><summary><a id="law-Engine.World.store_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L230">Engine.World.store_conns</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.World.fanout_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L214">Engine.World.fanout_conns</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.put_held"></a>▫️ <a href="../../engine/world/Hops.lean#L239">Engine.World.put_held</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_held"></a>▫️ <a href="../../engine/world/Hops.lean#L187">Engine.World.write_held</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_cases"></a>▫️ <a href="../../engine/world/Hops.lean#L91">Engine.World.recv_cases</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Sync.onHold_take">Engine.Sync.onHold_take</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L398">Engine.Sync.Conn.start_drop</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L403">Engine.Sync.Conn.start_take</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Hops.lean#L154">Engine.World.conn_isSome</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_sends"></a>▫️ <a href="../../engine/world/Asks.lean#L519">Engine.World.finish_sends</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>🌐 <a href="#law-Engine.Sync.seal_mem">Engine.Sync.seal_mem</a> ↪ · 35 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.asksOf_hold"></a>▫️ <a href="../../engine/world/Asks.lean#L572">Engine.World.asksOf_hold</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li><details><summary><a id="law-Engine.World.apply_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L467">Engine.World.apply_facts</a> · 27 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Asks.lean#L455">Engine.World.conn_replace</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.World.recv_asked">Engine.World.recv_asked</a> ↪ · 20 below</li>
<li>✅ <a href="#law-Engine.World.onHold_wants">Engine.World.onHold_wants</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 13 below</li>
<li><details><summary><a id="law-Engine.World.heldIn_turnH"></a>▫️ <a href="../../engine/world/Asks.lean#L582">Engine.World.heldIn_turnH</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.World.turnH_some"></a>▫️ <a href="../../engine/world/Hops.lean#L75">Engine.World.turnH_some</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.World.foldl_ingestS_some"></a>▫️ <a href="../../engine/world/Plain.lean#L48">Engine.World.foldl_ingestS_some</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Plain.lean#L39">Engine.World.ingestS_some</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.apply_reads">Engine.Sync.apply_reads</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.World.serveOwed_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L504">Engine.World.serveOwed_facts</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.onHold_take">Engine.Sync.onHold_take</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.forIn_suffix"></a>▫️ <a href="../../engine/world/Asks.lean#L538">Engine.World.forIn_suffix</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
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
<li>▫️ <a href="../../engine/world/Asks.lean#L24">Engine.World.WantsOn.append_left</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L29">Engine.World.WantsOn.append_right</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L578">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L575">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_queues"></a>🌐 <a href="../../engine/world/Owed.lean#L234">Engine.World.onSealed_queues</a> · 166 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.node_serve">Engine.World.node_serve</a> ↪ · 50 below</li>
<li>▫️ <a href="#law-Engine.World.payload_run">Engine.World.payload_run</a> ↪ · 49 below</li>
<li>▫️ <a href="#law-Engine.World.finish_sends">Engine.World.finish_sends</a> ↪ · 46 below</li>
<li><details><summary><a id="law-Engine.World.recv_want"></a>▫️ <a href="../../engine/world/Owed.lean#L119">Engine.World.recv_want</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.ofOp_want">Engine.Sync.ofOp_want</a> ↪ · 39 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.wantsOf_want"></a>▫️ <a href="../../engine/world/Owed.lean#L35">Engine.World.wantsOf_want</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.ofOp_want">Engine.Sync.ofOp_want</a> ↪ · 39 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_conn"></a>▫️ <a href="../../engine/world/Owed.lean#L220">Engine.World.finish_conn</a> · 40 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>▫️ <a href="../../engine/world/Owed.lean#L205">Engine.World.find_map_owed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.apply_ix"></a>▫️ <a href="../../engine/world/Owed.lean#L136">Engine.World.apply_ix</a> · 29 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.fanout_ix">Engine.World.fanout_ix</a> ↪ · 16 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.write_ix">Engine.Sync.write_ix</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.apply_facts">Engine.World.apply_facts</a> ↪ · 27 below</li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 13 below</li>
<li>✅ <a href="#law-Engine.World.recv_owed">Engine.World.recv_owed</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Engine.Sync.onWant_all">Engine.Sync.onWant_all</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.serveOwed_facts">Engine.World.serveOwed_facts</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.forIn_suffix">Engine.World.forIn_suffix</a> ↪ · 1 below</li>
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
<li>✅ <a href="../../engine/sync/ServeLaws.lean#L288">Engine.Sync.authorize_mem</a></li>
<li>✅ <a href="../../engine/sync/ServeLaws.lean#L330">Engine.Sync.onWant_order</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L578">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L575">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_takes"></a>🌐 <a href="../../engine/world/Hops.lean#L334">Engine.World.onSealed_takes</a> · 113 below</summary><ul>
<li><details><summary><a id="law-Engine.World.payload_takes"></a>▫️ <a href="../../engine/world/Hops.lean#L309">Engine.World.payload_takes</a> · 91 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.recv_data">Engine.Sync.recv_data</a> ↪ · 45 below</li>
<li><details><summary><a id="law-Engine.World.apply_one_held"></a>▫️ <a href="../../engine/world/Hops.lean#L275">Engine.World.apply_one_held</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.apply_store">Engine.World.apply_store</a> ↪ · 40 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.apply_takes">Engine.Sync.apply_takes</a> ↪ · 29 below</li>
<li>▫️ <a href="#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.payload_run">Engine.World.payload_run</a> ↪ · 49 below</li>
<li>▫️ <a href="#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.World.turnH_one_ops"></a>▫️ <a href="../../engine/world/Hops.lean#L81">Engine.World.turnH_one_ops</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.forIn_after"></a>▫️ <a href="../../engine/world/Hops.lean#L31">Engine.World.forIn_after</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
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
<li><details><summary><a id="law-Engine.World.onHold_wants"></a>✅ <a href="../../engine/world/Asks.lean#L173">Engine.World.onHold_wants</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.World.admitAsks_mem"></a>▫️ <a href="../../engine/world/Asks.lean#L101">Engine.World.admitAsks_mem</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.chunks_want"></a>▫️ <a href="../../engine/world/Asks.lean#L112">Engine.World.chunks_want</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Asks.lean#L118">Engine.World.wantStep_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_asked"></a>✅ <a href="../../engine/world/Asks.lean#L258">Engine.World.recv_asked</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.World.rbsr_asked"></a>▫️ <a href="../../engine/world/Asks.lean#L236">Engine.World.rbsr_asked</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.World.admit_goal"></a>▫️ <a href="../../engine/world/Asks.lean#L220">Engine.World.admit_goal</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.World.admitAsks_length"></a>▫️ <a href="../../engine/world/Asks.lean#L88">Engine.World.admitAsks_length</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.chunks_want">Engine.World.chunks_want</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.World.foldl_insert_mem"></a>▫️ <a href="../../engine/world/Asks.lean#L57">Engine.World.foldl_insert_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.foldl_insert_size"></a>▫️ <a href="../../engine/world/Asks.lean#L76">Engine.World.foldl_insert_size</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L189">Engine.World.answer_wants_le</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.admitAsks_length">Engine.World.admitAsks_length</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.World.chunks_want">Engine.World.chunks_want</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_mem">Engine.World.foldl_insert_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_size">Engine.World.foldl_insert_size</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L464">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L444">Engine.Sync.Conn.start_conn</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L118">Engine.World.wantStep_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_owed"></a>✅ <a href="../../engine/world/Owed.lean#L57">Engine.World.recv_owed</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_mem">Engine.World.foldl_insert_mem</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L464">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L444">Engine.Sync.Conn.start_conn</a></li>
<li>▫️ <a href="../../engine/world/Owed.lean#L42">Engine.World.onRbsr_owed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.node_serve"></a>🌐 <a href="../../engine/world/Owed.lean#L164">Engine.World.node_serve</a> · 50 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>✅ <a href="#law-Engine.Sync.serveOwed_hot">Engine.Sync.serveOwed_hot</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.Sync.serve_pending"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L21">Engine.Sync.serve_pending</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.serve_head">Engine.Sync.serve_head</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/TimeLaws.lean#L9">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L32">Engine.Sync.serve_zero</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L455">Engine.World.conn_replace</a></li>
</ul></details></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.Sync.has_of_mem"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L489">Engine.Sync.has_of_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_store"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L23">Engine.Sync.write_store</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.sealRetries_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L316">Engine.Sync.sealRetries_reads</a> · 34 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 33 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Reads.forIn-">Engine.Sync.Reads.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.seal_reads"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L313">Engine.Sync.seal_reads</a> · 33 below</summary><ul>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L130">Engine.Sync.Reads.bind'</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L129">Engine.Sync.Reads.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.forIn_yield"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L115">Engine.Sync.forIn_yield</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.write_goes"></a>▫️ <a href="../../app/Proofs.lean#L2788">Connection.Execution.NodeTape.write_goes</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.getOp-"></a>▫️ <a href="../../app/Proofs.lean#L2665">Connection.Execution.GoesM.getOp'</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2170">Connection.Execution.ReadsHeld.getOp'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Connection.Execution.GoesM.turn-"></a>▫️ <a href="../../app/Proofs.lean#L2669">Connection.Execution.GoesM.turn'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/EgressLaws.lean#L50">Engine.Sync.Moves.single</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.NodeTape.closure_reads"></a>▫️ <a href="../../app/Proofs.lean#L2743">Connection.Execution.NodeTape.closure_reads</a> · 6 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L2155">Connection.Execution.ReadsHeld.bind'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2170">Connection.Execution.ReadsHeld.getOp'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2154">Connection.Execution.ReadsHeld.pure'</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L103">Engine.Sync.closureOps_cons</a></li>
<li>▫️ <a href="../../engine/sync/Closure.lean#L32">Engine.Sync.closureOps_nil</a></li>
<li>▫️ <a href="../../engine/sync/SimLaws.lean#L116">Engine.Sync.closureOps_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.ReadsHeld.forIn-"></a>▫️ <a href="../../app/Proofs.lean#L2159">Connection.Execution.ReadsHeld.forIn'</a> · 2 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L2155">Connection.Execution.ReadsHeld.bind'</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L2154">Connection.Execution.ReadsHeld.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.turn_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L55">Engine.World.turn_keeps</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_ingestS_some">Engine.World.foldl_ingestS_some</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.purge_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L63">Engine.World.purge_keeps</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_asked"></a>▫️ <a href="../../engine/world/Asks.lean#L397">Engine.World.fanout_asked</a> · 18 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.fanout_facts">Engine.World.fanout_facts</a> ↪ · 16 below</li>
<li><details><summary><a id="law-Engine.World.filed_shape"></a>▫️ <a href="../../engine/world/Asks.lean#L330">Engine.World.filed_shape</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L368">Engine.World.fanout_facts</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.write_addrs"></a>▫️ <a href="../../engine/world/Hops.lean#L182">Engine.World.write_addrs</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_shape"></a>▫️ <a href="../../engine/world/Hops.lean#L158">Engine.World.write_shape</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.write_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L177">Engine.World.write_conns</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.write_shape">Engine.World.write_shape</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.foldl_erase_mem"></a>▫️ <a href="../../engine/world/InvIx.lean#L310">Engine.World.foldl_erase_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.close_conn"></a>▫️ <a href="../../engine/world/InvIx.lean#L250">Engine.World.close_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvIx.lean#L230">Engine.World.find_close</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.ask_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L272">Engine.World.ask_q</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L455">Engine.Sync.Conn.ask_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.start_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L269">Engine.World.start_q</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L444">Engine.Sync.Conn.start_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.covers_foldl"></a>▫️ <a href="../../engine/world/InvIx.lean#L465">Engine.World.covers_foldl</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_key">Engine.Sync.items_foldl_key</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.keyOf_id">Engine.Sync.keyOf_id</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.keyed_foldl"></a>▫️ <a href="../../engine/world/InvIx.lean#L456">Engine.World.keyed_foldl</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.mem_items_foldl">Engine.Sync.mem_items_foldl</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.foldl_ingestS_isSome"></a>▫️ <a href="../../engine/world/InvIx.lean#L490">Engine.World.foldl_ingestS_isSome</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L297">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
</ul>
