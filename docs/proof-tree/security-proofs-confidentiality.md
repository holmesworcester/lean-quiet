# Security proofs › Confidentiality

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Security proofs › Confidentiality**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1273) · 🌐 world: the node's code in a World (70) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (305) · 🧪 control: a negative control (32) · ▫️ lemma: not audited (2292)

<ul>
<li><details><summary><a id="law-Engine.Sync.recv_send"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L191">Engine.Sync.recv_send</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onHold_send"></a>▫️ <a href="../../engine/sync/ConnLaws.lean#L106">Engine.Sync.onHold_send</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.chunks_wire"></a>▫️ <a href="../../engine/sync/ConnLaws.lean#L26">Engine.Sync.chunks_wire</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onRbsr_send"></a>▫️ <a href="../../engine/sync/ConnLaws.lean#L76">Engine.Sync.onRbsr_send</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.chunks_wire">Engine.Sync.chunks_wire</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onWant_send"></a>▫️ <a href="../../engine/sync/ConnLaws.lean#L117">Engine.Sync.onWant_send</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L338">Engine.Sync.onWant_silent</a></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L346">Engine.Sync.onWant_take</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.start_send"></a>▫️ <a href="../../engine/sync/ConnLaws.lean#L40">Engine.Sync.start_send</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L132">Engine.Sync.recv_cases</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L38">Engine.Sync.shows_heard</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.hold_reply_local"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L573">Engine.Sync.hold_reply_local</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onHold_local"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L554">Engine.Sync.onHold_local</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onHold_apply"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L285">Engine.Sync.onHold_apply</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.holdsIn_apply"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L274">Engine.Sync.holdsIn_apply</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.HeldM.forIn_reads"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L34">Engine.Sync.HeldM.forIn_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/OfferLaws.lean#L531">Engine.Sync.heldIn_local</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.heldIn_index"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L594">Engine.Sync.heldIn_index</a> · 82 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.cached_items">Engine.Sync.cached_items</a> ↪ · 81 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.hold_reply_local_premises"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L619">Engine.Sync.hold_reply_local_premises</a> · 44 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Codec.decFromAs_tag"></a>▫️ <a href="../../engine/core/Codec.lean#L716">Engine.Codec.decFromAs_tag</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.cons">Engine.Codec.At.cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
</ul></details></li>
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
<li><details><summary><a id="law-Engine.Sync.onWant_authorized"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L296">Engine.Sync.onWant_authorized</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/sync/ServeLaws.lean#L288">Engine.Sync.authorize_mem</a></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L271">Engine.Sync.instLawfulBEqByteArray_engine</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_blind"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L493">Engine.Sync.serveOwed_blind</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_blind"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L115">Engine.Sync.serve_blind</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_cons"></a>▫️ <a href="../../engine/sync/ServeLaws.lean#L36">Engine.Sync.serve_cons</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Serve.lean#L30">Engine.Sync.Read.trace_map</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L32">Engine.Sync.serve_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.fetch_blind"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L250">Engine.Sync.fetch_blind</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fetch_cons"></a>▫️ <a href="../../engine/sync/ServeLaws.lean#L201">Engine.Sync.fetch_cons</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Serve.lean#L30">Engine.Sync.Read.trace_map</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_eq"></a>▫️ <a href="../../engine/sync/ServeLaws.lean#L369">Engine.Sync.serveOwed_eq</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/ServeLaws.lean#L12">Engine.Sync.Read.run_held</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L271">Engine.Sync.instLawfulBEqByteArray_engine</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_shown"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L476">Engine.Sync.serveOwed_shown</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_shown"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L86">Engine.Sync.serve_shown</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L32">Engine.Sync.serve_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.fetch_shown"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L216">Engine.Sync.fetch_shown</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.fetch_cons">Engine.Sync.fetch_cons</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_run"></a>▫️ <a href="../../engine/sync/ServeLaws.lean#L377">Engine.Sync.serveOwed_run</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L271">Engine.Sync.instLawfulBEqByteArray_engine</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.offer_shared"></a>✅ <a href="../../engine/sync/SecrecyLaws.lean#L64">Engine.Sync.offer_shared</a> · 49 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.holdsOf_shown"></a>✅ <a href="../../engine/sync/SecrecyLaws.lean#L46">Engine.Sync.holdsOf_shown</a> · 42 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOp_hold"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L521">Engine.Sync.ofOp_hold</a> · 40 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
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
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L80">Engine.Sync.mem_pieceIds</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_origin"></a>✅ <a href="../../engine/sync/SecrecyLaws.lean#L12">Engine.Sync.filed_origin</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L252">Engine.Sync.foldl_inv</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L60">Engine.Sync.shows_rooms</a></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Connection.wire_kinds"></a>✅ <a href="../../app/connection/Proofs.lean#L44">Connection.wire_kinds</a></li>
<li><a id="law-Connection.local_kinds"></a>✅ <a href="../../app/connection/Proofs.lean#L51">Connection.local_kinds</a></li>
<li><details><summary><a id="law-Community.joinOps_travels"></a>✅ <a href="../../app/community/Proofs.lean#L334">Community.joinOps_travels</a> · 44 below</summary><ul>
<li><details><summary><a id="law-Community.shared_mkOp"></a>▫️ <a href="../../app/community/Family.lean#L1539">Community.shared_mkOp</a> · 43 below</summary><ul>
<li><details><summary><a id="law-Community.body_mkOp"></a>▫️ <a href="../../app/community/Family.lean#L1536">Community.body_mkOp</a> · 41 below</summary><ul>
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
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
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
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/community/Family.lean#L1257">Community.Body.local_of_ephemeral</a></li>
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
</ul></details></li>
<li><details><summary><a id="law-Community.found_travels"></a>✅ <a href="../../app/community/Proofs.lean#L341">Community.found_travels</a> · 47 below</summary><ul>
<li><details><summary><a id="law-Community.nodeKeyOr_local"></a>✅ <a href="../../app/community/device/endpoint/Proofs.lean#L8">Community.nodeKeyOr_local</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Community.shared_mkOp">Community.shared_mkOp</a> ↪ · 43 below</li>
<li><details><summary><a id="law-Engine.View.eval_bind-"></a>▫️ <a href="../../engine/core/View.lean#L68">Engine.View.eval_bind'</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Community.shared_mkOp">Community.shared_mkOp</a> ↪ · 43 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.stopWaiting_local"></a>✅ <a href="../../app/community/member/join/joining/abandon/Proofs.lean#L8">Community.stopWaiting_local</a> · 44 below</summary><ul>
<li>▫️ <a href="#law-Community.shared_mkOp">Community.shared_mkOp</a> ↪ · 43 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_send"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L225">Engine.Sync.filed_send</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.holdsOf_wire"></a>▫️ <a href="../../engine/sync/ConnLaws.lean#L98">Engine.Sync.holdsOf_wire</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.chunks_wire">Engine.Sync.chunks_wire</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.offer_stored"></a>✅ <a href="../../engine/sync/SecrecyLaws.lean#L78">Engine.Sync.offer_stored</a> · 50 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.offer_shared">Engine.Sync.offer_shared</a> ↪ · 49 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_send"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L245">Engine.Sync.tick_send</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.work_send"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L233">Engine.Sync.work_send</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.due_send"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L69">Engine.Sync.due_send</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ask_send"></a>✅ <a href="../../engine/sync/ConnLaws.lean#L54">Engine.Sync.ask_send</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.start_send">Engine.Sync.start_send</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.chunks_wire">Engine.Sync.chunks_wire</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L487">Engine.Sync.Step.pulse_take</a></li>
<li>▫️ <a href="../../engine/sync/ConnLaws.lean#L20">Engine.Sync.msg_wire</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.recipients_iff"></a>📐 <a href="../../app/community/Proofs.lean#L894">Community.recipients_iff</a> · 69 below</summary><ul>
<li><details><summary><a id="law-Community.mem_live_all"></a>▫️ <a href="../../app/community/Proofs.lean#L872">Community.mem_live_all</a> · 68 below</summary><ul>
<li><details><summary><a id="law-Community.live_iff"></a>▫️ <a href="../../app/community/Proofs.lean#L813">Community.live_iff</a> · 66 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.deviceLive_iff">Community.deviceLive_iff</a> ↪ · 62 below</li>
<li><details><summary><a id="law-Community.exists_row"></a>▫️ <a href="../../app/community/Proofs.lean#L643">Community.exists_row</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Community.filed"></a>▫️ <a href="../../app/community/Family.lean#L1582">Community.filed</a> · 48 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.filed_rel">Engine.filed_rel</a> ↪ · 45 below</li>
<li>✅ <a href="../../app/community/Family.lean#L1575">Community.rels_distinct</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1577">Community.rels_short</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_rows_all"></a>▫️ <a href="../../engine/core/Decl.lean#L180">Engine.mem_rows_all</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.mem_live"></a>▫️ <a href="../../app/community/Proofs.lean#L765">Community.mem_live</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Community.eval_live_adm"></a>▫️ <a href="../../app/community/Proofs.lean#L755">Community.eval_live_adm</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.View.eval_bind-">Engine.View.eval_bind'</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L657">Community.mem_cons_row</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Proofs.lean#L623">Community.all_args</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.members_iff"></a>📐 <a href="../../app/community/Proofs.lean#L881">Community.members_iff</a> · 69 below</summary><ul>
<li>▫️ <a href="#law-Community.mem_live_all">Community.mem_live_all</a> ↪ · 68 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.member_reads"></a>✅ <a href="../../app/community/Proofs.lean#L316">Community.member_reads</a> · 52 below</summary><ul>
<li>✅ <a href="#law-Community.sealedPost_opens">Community.sealedPost_opens</a> ↪ · 48 below</li>
<li>✅ <a href="#law-Community.wrapKey_opens">Community.wrapKey_opens</a> ↪ · 46 below</li>
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
<li><details><summary><a id="law-Community.sealedPost_opens"></a>✅ <a href="../../app/community/Proofs.lean#L285">Community.sealedPost_opens</a> · 48 below</summary><ul>
<li>▫️ <a href="#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
<li><details><summary><a id="law-Community.bodyAd_size"></a>✅ <a href="../../app/community/Proofs.lean#L270">Community.bodyAd_size</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.Codec.length_enc_bytes"></a>▫️ <a href="../../engine/core/Codec.lean#L794">Engine.Codec.length_enc_bytes</a> · 24 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L152">Engine.Codec.encNat_small</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>✅ <a href="#law-Community.openSealed_seal">Community.openSealed_seal</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/community/Op.lean#L149">Community.cryptoSeal_good</a></li>
<li>✅ <a href="../../engine/core/Crypto.lean#L33">Engine.Bytes.of?_val</a></li>
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
<li><details><summary><a id="law-Community.wrapKey_opens"></a>✅ <a href="../../app/community/Proofs.lean#L303">Community.wrapKey_opens</a> · 46 below</summary><ul>
<li>▫️ <a href="#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>✅ <a href="#law-Community.unbox_box">Community.unbox_box</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/community/Op.lean#L149">Community.cryptoSeal_good</a></li>
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
<li><details><summary><a id="law-Community.member_opens"></a>✅ <a href="../../app/community/Proofs.lean#L258">Community.member_opens</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Community.unbox_box">Community.unbox_box</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Community.openSealed_seal">Community.openSealed_seal</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.openSealed_seal"></a>✅ <a href="../../app/community/Proofs.lean#L243">Community.openSealed_seal</a> · 1 below</summary><ul>
<li>✅ <a href="../../app/community/Op.lean#L112">Community.openBody_sealBody</a></li>
</ul></details></li>
<li><a id="law-Community.openBody_sealBody"></a>✅ <a href="../../app/community/Op.lean#L112">Community.openBody_sealBody</a></li>
<li><details><summary><a id="law-Community.unbox_box"></a>✅ <a href="../../app/community/Op.lean#L121">Community.unbox_box</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Community.boxKey_of"></a>✅ <a href="../../app/community/Op.lean#L116">Community.boxKey_of</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Crypto.lean#L33">Engine.Bytes.of?_val</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Crypto.lean#L33">Engine.Bytes.of?_val</a></li>
</ul></details></li>
<li><a id="law-Community.cryptoSeal_good"></a>✅ <a href="../../app/community/Op.lean#L149">Community.cryptoSeal_good</a></li>
<li><details><summary><a id="law-Community.check_reads_shared"></a>📐 <a href="../../app/community/Proofs.lean#L193">Community.check_reads_shared</a> · 34 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Community.counterOk_shared"></a>▫️ <a href="../../app/community/name/Proofs.lean#L25">Community.counterOk_shared</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/name/Proofs.lean#L7">Community.prevMax_shared</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/member/admin/Proofs.lean#L51">Community.isAdmin_shared</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.approveReq_wrap_admits"></a>✅ <a href="../../app/community/Proofs.lean#L1345">Community.approveReq_wrap_admits</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/key/wrap/Proofs.lean#L11">Engine.View.always_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_secret"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L629">Connection.Noise.Symbolic.kk_secret</a> · 29 below</summary><ul>
<li>✅ <a href="#law-Connection.Noise.Symbolic.kk_secret_init">Connection.Noise.Symbolic.kk_secret_init</a> ↪ · 24 below</li>
<li>✅ <a href="#law-Connection.Noise.Symbolic.kk_secret_resp">Connection.Noise.Symbolic.kk_secret_resp</a> ↪ · 23 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L616">Connection.Noise.Symbolic.exposed_clean</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_secret_init"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L581">Connection.Noise.Symbolic.kk_secret_init</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.keys_secret"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L555">Connection.Noise.Symbolic.keys_secret</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.not_derivable"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L552">Connection.Noise.Symbolic.not_derivable</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.derivable_clean"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L478">Connection.Noise.Symbolic.derivable_clean</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.sends_clean"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L444">Connection.Noise.Symbolic.sends_clean</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.clean_decHash">Connection.Noise.Symbolic.clean_decHash</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L432">Connection.Noise.Symbolic.clean_encHash</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L424">Connection.Noise.Symbolic.clean_one</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L428">Connection.Noise.Symbolic.clean_two</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L310">Connection.Noise.Symbolic.unpair_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L152">Connection.Noise.read1_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L138">Connection.Noise.write1_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L198">Connection.Noise.write2_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.reveals_clean"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L461">Connection.Noise.Symbolic.reveals_clean</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.clean_decHash">Connection.Noise.Symbolic.clean_decHash</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L424">Connection.Noise.Symbolic.clean_one</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L428">Connection.Noise.Symbolic.clean_two</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L310">Connection.Noise.Symbolic.unpair_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L152">Connection.Noise.read1_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L215">Connection.Noise.read2_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L175">Connection.Noise.sent1_some</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L417">Connection.Noise.Symbolic.clean_dh</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L293">Connection.Noise.Symbolic.dh_some</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L546">Connection.Noise.Symbolic.keys_unclean</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.init_unclean"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L564">Connection.Noise.Symbolic.init_unclean</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.sent1_ck"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L509">Connection.Noise.Symbolic.sent1_ck</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L310">Connection.Noise.Symbolic.unpair_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L128">Connection.Noise.decHash_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L175">Connection.Noise.sent1_some</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L417">Connection.Noise.Symbolic.clean_dh</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.read2_keys"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L524">Connection.Noise.Symbolic.read2_keys</a> · 4 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L300">Connection.Noise.Symbolic.dec_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L310">Connection.Noise.Symbolic.unpair_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L128">Connection.Noise.decHash_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L215">Connection.Noise.read2_some</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_secret_resp"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L594">Connection.Noise.Symbolic.kk_secret_resp</a> · 23 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.keys_secret">Connection.Noise.Symbolic.keys_secret</a> ↪ · 19 below</li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.read1_ck"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L516">Connection.Noise.Symbolic.read1_ck</a> · 4 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L300">Connection.Noise.Symbolic.dec_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L310">Connection.Noise.Symbolic.unpair_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L128">Connection.Noise.decHash_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L152">Connection.Noise.read1_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.write2_keys"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L536">Connection.Noise.Symbolic.write2_keys</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L198">Connection.Noise.write2_some</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L417">Connection.Noise.Symbolic.clean_dh</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_secret_init_tight"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L650">Connection.Noise.Symbolic.kk_secret_init_tight</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read2_keys">Connection.Noise.Symbolic.read2_keys</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.sent1_ck">Connection.Noise.Symbolic.sent1_ck</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L293">Connection.Noise.Symbolic.dh_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_runs"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L329">Connection.Noise.Symbolic.kk_runs</a> · 11 below</summary><ul>
<li>✅ <a href="#law-Connection.Noise.handshake_agrees">Connection.Noise.handshake_agrees</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
<li>📐 <a href="../../engine/wire/NoiseSymbolic.lean#L318">Connection.Noise.Symbolic.good</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.handshake_agrees"></a>✅ <a href="../../engine/wire/Noise.lean#L363">Connection.Noise.handshake_agrees</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.read1_write1"></a>▫️ <a href="../../engine/wire/Noise.lean#L252">Connection.Noise.read1_write1</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.one_valid"></a>▫️ <a href="../../engine/wire/Noise.lean#L229">Connection.Noise.one_valid</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/Noise.lean#L226">Connection.Noise.mixKey_valid</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/Noise.lean#L246">Connection.Noise.decHash_encHash</a></li>
<li>▫️ <a href="../../engine/wire/Noise.lean#L235">Connection.Noise.one_ad</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.read2_write2"></a>▫️ <a href="../../engine/wire/Noise.lean#L279">Connection.Noise.read2_write2</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.two_valid"></a>▫️ <a href="../../engine/wire/Noise.lean#L232">Connection.Noise.two_valid</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/Noise.lean#L226">Connection.Noise.mixKey_valid</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/Noise.lean#L246">Connection.Noise.decHash_encHash</a></li>
<li>▫️ <a href="../../engine/wire/Noise.lean#L238">Connection.Noise.two_ad</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_authentic"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L933">Connection.Noise.Symbolic.kk_authentic</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Connection.Noise.Symbolic.kk_agree">Connection.Noise.Symbolic.kk_agree</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_agree"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L867">Connection.Noise.Symbolic.kk_agree</a> · 30 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.derivable_sealed"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L825">Connection.Noise.Symbolic.derivable_sealed</a> · 23 below</summary><ul>
<li>✅ <a href="#law-Connection.Noise.Symbolic.derivable_clean">Connection.Noise.Symbolic.derivable_clean</a> ↪ · 16 below</li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.reveals_sealed"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L810">Connection.Noise.Symbolic.reveals_sealed</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read1_ck">Connection.Noise.Symbolic.read1_ck</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read2_keys">Connection.Noise.Symbolic.read2_keys</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.sends_sealed"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L780">Connection.Noise.Symbolic.sends_sealed</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.write1_msg"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L504">Connection.Noise.Symbolic.write1_msg</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L138">Connection.Noise.write1_some</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write2_keys">Connection.Noise.Symbolic.write2_keys</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L293">Connection.Noise.Symbolic.dh_some</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.init_unclean">Connection.Noise.Symbolic.init_unclean</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read1_ck">Connection.Noise.Symbolic.read1_ck</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read2_keys">Connection.Noise.Symbolic.read2_keys</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.sent1_ck">Connection.Noise.Symbolic.sent1_ck</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write1_msg">Connection.Noise.Symbolic.write1_msg</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write2_keys">Connection.Noise.Symbolic.write2_keys</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L293">Connection.Noise.Symbolic.dh_some</a></li>
<li>📐 <a href="../../engine/wire/NoiseSymbolic.lean#L318">Connection.Noise.Symbolic.good</a></li>
<li>✅ <a href="../../engine/wire/Noise.lean#L326">Connection.Noise.read2_write2'</a></li>
<li>✅ <a href="../../engine/wire/Noise.lean#L295">Connection.Noise.sent1_read1</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_authentic_resp"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L1018">Connection.Noise.Symbolic.kk_authentic_resp</a> · 33 below</summary><ul>
<li>✅ <a href="#law-Connection.Noise.Symbolic.kk_agree_resp">Connection.Noise.Symbolic.kk_agree_resp</a> ↪ · 32 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_agree_resp"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L956">Connection.Noise.Symbolic.kk_agree_resp</a> · 32 below</summary><ul>
<li>✅ <a href="#law-Connection.Noise.Symbolic.derivable_sealed">Connection.Noise.Symbolic.derivable_sealed</a> ↪ · 23 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read1_ck">Connection.Noise.Symbolic.read1_ck</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read2_keys">Connection.Noise.Symbolic.read2_keys</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Connection.Noise.sent1_write1"></a>✅ <a href="../../engine/wire/Noise.lean#L264">Connection.Noise.sent1_write1</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.one_valid">Connection.Noise.one_valid</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/Noise.lean#L246">Connection.Noise.decHash_encHash</a></li>
<li>▫️ <a href="../../engine/wire/Noise.lean#L235">Connection.Noise.one_ad</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write1_msg">Connection.Noise.Symbolic.write1_msg</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write2_keys">Connection.Noise.Symbolic.write2_keys</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L417">Connection.Noise.Symbolic.clean_dh</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
<li>📐 <a href="../../engine/wire/NoiseSymbolic.lean#L318">Connection.Noise.Symbolic.good</a></li>
<li>✅ <a href="../../engine/wire/Noise.lean#L295">Connection.Noise.sent1_read1</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_authentic_tight"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L1035">Connection.Noise.Symbolic.kk_authentic_tight</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.read2_write2">Connection.Noise.read2_write2</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.sent1_ck">Connection.Noise.Symbolic.sent1_ck</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write2_keys">Connection.Noise.Symbolic.write2_keys</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L774">Connection.Noise.Symbolic.dh_swap</a></li>
<li>📐 <a href="../../engine/wire/NoiseSymbolic.lean#L318">Connection.Noise.Symbolic.good</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_authentic_resp_tight"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L1070">Connection.Noise.Symbolic.kk_authentic_resp_tight</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.read1_write1">Connection.Noise.read1_write1</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L774">Connection.Noise.Symbolic.dh_swap</a></li>
<li>📐 <a href="../../engine/wire/NoiseSymbolic.lean#L318">Connection.Noise.Symbolic.good</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L138">Connection.Noise.write1_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.close_forgets"></a>✅ <a href="../../app/Proofs.lean#L3830">Connection.close_forgets</a> · 122 below</summary><ul>
<li>✅ <a href="#law-Connection.purge_forgets">Connection.purge_forgets</a> ↪ · 117 below</li>
<li><details><summary><a id="law-Connection.purge_uncited"></a>▫️ <a href="../../app/Proofs.lean#L3775">Connection.purge_uncited</a> · 26 below</summary><ul>
<li><details><summary><a id="law-Engine.closeUp_closed"></a>▫️ <a href="../../engine/core/Purge.lean#L306">Engine.closeUp_closed</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.closeUp_walk"></a>▫️ <a href="../../engine/core/Purge.lean#L282">Engine.closeUp_walk</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.walkS_ends"></a>▫️ <a href="../../engine/core/Purge.lean#L257">Engine.walkS_ends</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.WalkInv.step">Engine.WalkInv.step</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L189">Engine.WalkInv.length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.pushNew_spec"></a>▫️ <a href="../../engine/core/Purge.lean#L99">Engine.pushNew_spec</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L79">Engine.byteArray_beq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_dependents"></a>▫️ <a href="../../engine/core/Purge.lean#L85">Engine.mem_dependents</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_sortIds"></a>▫️ <a href="../../engine/core/Model.lean#L73">Engine.mem_sortIds</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.closeUp_sub"></a>▫️ <a href="../../engine/core/Purge.lean#L301">Engine.closeUp_sub</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_walk">Engine.closeUp_walk</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purgeCappedS_ops"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L640">Engine.purgeCappedS_ops</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.urgentCloseS_ops"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L527">Engine.urgentCloseS_ops</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.judgeAheadS_ops"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L516">Engine.judgeAheadS_ops</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L96">Engine.judgeAheadS_eq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.drainS_ops"></a>▫️ <a href="../../engine/core/Budget.lean#L191">Engine.drainS_ops</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purgeS_ops_mem"></a>▫️ <a href="../../engine/core/Purge.lean#L393">Engine.purgeS_ops_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purgeS_ops_not"></a>▫️ <a href="../../engine/core/Purge.lean#L398">Engine.purgeS_ops_not</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L3814">Connection.closing_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>✅ <a href="../../engine/wire/CloseLaws.lean#L14">Engine.Sync.endSession_purges</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L484">Engine.Sync.purge_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.purge_forgets"></a>✅ <a href="../../app/Proofs.lean#L3798">Connection.purge_forgets</a> · 117 below</summary><ul>
<li><details><summary><a id="law-Engine.inv_purgeCapped"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L648">Engine.inv_purgeCapped</a> · 59 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.purge_inv">Engine.purge_inv</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Engine.inv_urgentClose"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L580">Engine.inv_urgentClose</a> · 28 below</summary><ul>
<li><details><summary><a id="law-Engine.inv_judgeAhead"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L566">Engine.inv_judgeAhead</a> · 27 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L527">Engine.inv_front</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L96">Engine.judgeAheadS_eq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.inv_drainS"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L572">Engine.inv_drainS</a> · 25 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.forgets_of_uncited"></a>▫️ <a href="../../app/Proofs.lean#L3765">Connection.forgets_of_uncited</a> · 49 below</summary><ul>
<li><details><summary><a id="law-Connection.keyRow_op"></a>▫️ <a href="../../app/Proofs.lean#L3733">Connection.keyRow_op</a> · 48 below</summary><ul>
<li><details><summary><a id="law-Connection.validate_established"></a>▫️ <a href="../../app/Proofs.lean#L3699">Connection.validate_established</a> · 41 below</summary><ul>
<li><details><summary><a id="law-Connection.established_check"></a>▫️ <a href="../../app/Proofs.lean#L3655">Connection.established_check</a> · 28 below</summary><ul>
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
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Connection.Body.decFrom_of"></a>▫️ <a href="../../app/connection/Family.lean#L290">Connection.Body.decFrom_of</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
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
<li><details><summary><a id="law-Connection.validate_eph"></a>▫️ <a href="../../app/Proofs.lean#L3677">Connection.validate_eph</a> · 37 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Connection.Body.decFrom_of">Connection.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/connection/Family.lean#L281">Connection.Body.dec_of</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L3646">Connection.eph_check</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.valid_op"></a>▫️ <a href="../../app/Proofs.lean#L3604">Connection.valid_op</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L3588">Connection.allValid_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L3719">Connection.headD_mem</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L3726">Connection.room_local</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Connection.purge_uncited">Connection.purge_uncited</a> ↪ · 26 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.retired_complete"></a>✅ <a href="../../app/Proofs.lean#L3850">Connection.retired_complete</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Connection.openSessions_state"></a>▫️ <a href="../../app/Proofs.lean#L300">Connection.openSessions_state</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Connection.allSessions_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L243">Connection.allSessions_state</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Connection.sessionsOf_state"></a>▫️ <a href="../../app/connection/Proofs.lean#L236">Connection.sessionsOf_state</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/connection/Proofs.lean#L226">Connection.sessionOf_state</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.carrying_mem"></a>▫️ <a href="../../app/Proofs.lean#L273">Connection.carrying_mem</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/View.lean#L55">Engine.View.run_model</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.forget_stays"></a>✅ <a href="../../app/Proofs.lean#L3804">Connection.forget_stays</a> · 116 below</summary><ul>
<li>▫️ <a href="#law-Engine.inv_purgeCapped">Engine.inv_purgeCapped</a> ↪ · 59 below</li>
<li>▫️ <a href="#law-Connection.forgets_of_uncited">Connection.forgets_of_uncited</a> ↪ · 49 below</li>
<li><details><summary><a id="law-Connection.uncited_stays"></a>▫️ <a href="../../app/Proofs.lean#L3787">Connection.uncited_stays</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Engine.purgeCappedS_ops">Engine.purgeCappedS_ops</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Engine.Sync.close_purges"></a>✅ <a href="../../engine/wire/CloseLaws.lean#L36">Engine.Sync.close_purges</a></li>
<li><details><summary><a id="law-Engine.Sync.close_gone"></a>✅ <a href="../../engine/wire/CloseLaws.lean#L22">Engine.Sync.close_gone</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.purge_named">Engine.purge_named</a> ↪ · 18 below</li>
<li>▫️ <a href="#law-Engine.purgeCappedS_ops">Engine.purgeCappedS_ops</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>✅ <a href="../../engine/wire/CloseLaws.lean#L14">Engine.Sync.endSession_purges</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.drop_iff_silent"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L21">Engine.Sync.drop_iff_silent</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.work_no_drop"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L14">Engine.Sync.work_no_drop</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Conn.lean#L620">Engine.Sync.Conn.ask_drop</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L602">Engine.Sync.Conn.start_drop</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L489">Engine.Sync.Step.pulse_drop</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.keepalive_sent"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L30">Engine.Sync.keepalive_sent</a></li>
<li><details><summary><a id="law-Engine.Sync.live_stays"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L75">Engine.Sync.live_stays</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.peer_keeps_live"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L55">Engine.Sync.peer_keeps_live</a> · 6 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.drop_iff_silent">Engine.Sync.drop_iff_silent</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/sync/TimeLaws.lean#L38">Engine.Sync.tick_sends_or_recent</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.drop_iff_silent">Engine.Sync.drop_iff_silent</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_forward_secret"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L721">Connection.Noise.Symbolic.kk_forward_secret</a> · 28 below</summary><ul>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_forward_secret_resp"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L696">Connection.Noise.Symbolic.kk_forward_secret_resp</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.keys_secret">Connection.Noise.Symbolic.keys_secret</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read1_ck">Connection.Noise.Symbolic.read1_ck</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write1_msg">Connection.Noise.Symbolic.write1_msg</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write2_keys">Connection.Noise.Symbolic.write2_keys</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L417">Connection.Noise.Symbolic.clean_dh</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.kk_forward_secret_init"></a>✅ <a href="../../engine/wire/NoiseSymbolic.lean#L677">Connection.Noise.Symbolic.kk_forward_secret_init</a> · 23 below</summary><ul>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.keys_secret">Connection.Noise.Symbolic.keys_secret</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.read2_keys">Connection.Noise.Symbolic.read2_keys</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Connection.Noise.Symbolic.write2_keys">Connection.Noise.Symbolic.write2_keys</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L417">Connection.Noise.Symbolic.clean_dh</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L291">Connection.Noise.Symbolic.dh_atom</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L616">Connection.Noise.Symbolic.exposed_clean</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_named"></a>✅ <a href="../../engine/core/Purge.lean#L574">Engine.purge_named</a> · 18 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_sub">Engine.closeUp_sub</a> ↪ · 11 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.purge_gone">Engine.purge_gone</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.have_shown"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L475">Engine.Sync.have_shown</a> · 143 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L383">Engine.Sync.recv_keeps</a> · 106 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.onRbsr_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L194">Engine.Sync.onRbsr_keeps</a> · 86 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Index.answer_fun"></a>▫️ <a href="../../engine/sync/Conn.lean#L381">Engine.Sync.Index.answer_fun</a> · 77 below</summary><ul>
<li>✅ <a href="quality-proofs.md#law-Engine.Sync.Index.answer_eq">Engine.Sync.Index.answer_eq</a> ↪ · 76 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.answer_offers"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L124">Engine.Sync.answer_offers</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.chunks_hold"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L93">Engine.Sync.chunks_hold</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L80">Engine.Sync.mem_pieceIds</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.shown_item"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L74">Engine.Sync.shown_item</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L385">Engine.Sync.Index.over_sub</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L111">Engine.Sync.chunks_want</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.start_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L159">Engine.Sync.start_keeps</a> · 76 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Index.opening_fun"></a>▫️ <a href="../../engine/sync/Conn.lean#L378">Engine.Sync.Index.opening_fun</a> · 70 below</summary><ul>
<li>✅ <a href="quality-proofs.md#law-Engine.Sync.Index.opening_eq">Engine.Sync.Index.opening_eq</a> ↪ · 69 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.opening_offers"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L148">Engine.Sync.opening_offers</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/RoundLaws.lean#L44">Engine.Sync.mem_within</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.shown_item">Engine.Sync.shown_item</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L385">Engine.Sync.Index.over_sub</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.onHold_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L317">Engine.Sync.onHold_keeps</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L111">Engine.Sync.chunks_want</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.keeps_rooms"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L331">Engine.Sync.keeps_rooms</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.discloses_rooms"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L67">Engine.Sync.discloses_rooms</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.shown_rooms"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L63">Engine.Sync.shown_rooms</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L60">Engine.Sync.shows_rooms</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L60">Engine.Sync.shows_rooms</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.discloses_rooms">Engine.Sync.discloses_rooms</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.Conn.onAsk_rooms"></a>▫️ <a href="../../engine/sync/Conn.lean#L675">Engine.Sync.Conn.onAsk_rooms</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L668">Engine.Sync.Conn.onAsk_eq</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/OfferLaws.lean#L326">Engine.Sync.onWant_keeps</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.tick_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L443">Engine.Sync.tick_keeps</a> · 85 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.work_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L422">Engine.Sync.work_keeps</a> · 83 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.start_keeps">Engine.Sync.start_keeps</a> ↪ · 76 below</li>
<li>▫️ <a href="#law-Engine.Sync.discloses_rooms">Engine.Sync.discloses_rooms</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L27">Engine.Sync.HeldM.pure_apply</a></li>
<li>✅ <a href="../../engine/sync/OfferLaws.lean#L180">Engine.Sync.ask_keeps</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L111">Engine.Sync.chunks_want</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L485">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.cached_shown"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L57">Engine.Sync.cached_shown</a> · 82 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.cached_items">Engine.Sync.cached_items</a> ↪ · 81 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_keeps"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L345">Engine.Sync.filed_keeps</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.holdsOf_hold"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L100">Engine.Sync.holdsOf_hold</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.chunks_hold">Engine.Sync.chunks_hold</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L252">Engine.Sync.foldl_inv</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L60">Engine.Sync.shows_rooms</a></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Engine.Sync.boot_cached"></a>✅ <a href="../../engine/wire/NodeLaws.lean#L262">Engine.Sync.boot_cached</a></li>
<li><details><summary><a id="law-Engine.Sync.write_cached"></a>✅ <a href="../../engine/wire/NodeLaws.lean#L439">Engine.Sync.write_cached</a> · 57 below</summary><ul>
<li><details><summary><a id="law-Engine.inv_turnCapped"></a>✅ <a href="../../engine/core/TurnLaws.lean#L586">Engine.inv_turnCapped</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.inv_judgeJob"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L576">Engine.inv_judgeJob</a> · 28 below</summary><ul>
<li>▫️ <a href="#law-Engine.inv_judgeAhead">Engine.inv_judgeAhead</a> ↪ · 27 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.inv_urgentClose">Engine.inv_urgentClose</a> ↪ · 28 below</li>
<li>▫️ <a href="#law-Engine.inv_drainS">Engine.inv_drainS</a> ↪ · 25 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_ingest">Engine.inv_ingest</a> ↪ · 8 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.foldl_ingest_new"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L317">Engine.Sync.foldl_ingest_new</a> · 12 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.inv_ingest">Engine.inv_ingest</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.has_false"></a>▫️ <a href="../../engine/core/Model.lean#L53">Engine.has_false</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L249">Engine.Sync.filterMap_ext</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.turnCappedS_ops"></a>✅ <a href="../../engine/core/TurnLaws.lean#L535">Engine.turnCappedS_ops</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.judgeJobS_ops"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L521">Engine.judgeJobS_ops</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.judgeAheadS_ops">Engine.judgeAheadS_ops</a> ↪ · 8 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.urgentCloseS_ops">Engine.urgentCloseS_ops</a> ↪ · 9 below</li>
<li>▫️ <a href="#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.turnCappedS_stored"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L562">Engine.turnCappedS_stored</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.judgeJobS_stored"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L544">Engine.judgeJobS_stored</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.judgeAheadS_stored"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L539">Engine.judgeAheadS_stored</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.stepS_stored"></a>▫️ <a href="../../engine/core/Proofs.lean#L182">Engine.stepS_stored</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.decideS_stored">Engine.decideS_stored</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L34">Engine.waitOnS_stored</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L96">Engine.judgeAheadS_eq</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.urgentCloseS_stored"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L550">Engine.urgentCloseS_stored</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.judgeAheadS_stored">Engine.judgeAheadS_stored</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.drainS_stored-"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L557">Engine.drainS_stored'</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.stepS_stored">Engine.stepS_stored</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.absentOf_new"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L391">Engine.Sync.absentOf_new</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L41">Engine.Sync.bytes_beq_self</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L426">Engine.Sync.foldl_fileStep</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.purge_cached"></a>✅ <a href="../../engine/wire/NodeLaws.lean#L512">Engine.Sync.purge_cached</a> · 73 below</summary><ul>
<li>▫️ <a href="#law-Engine.inv_purgeCapped">Engine.inv_purgeCapped</a> ↪ · 59 below</li>
<li>▫️ <a href="#law-Engine.purgeCappedS_ops">Engine.purgeCappedS_ops</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.purgeCappedS_stored"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L644">Engine.purgeCappedS_stored</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.urgentCloseS_stored">Engine.urgentCloseS_stored</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.drainS_stored-">Engine.drainS_stored'</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filter_purged"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L489">Engine.Sync.filter_purged</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L235">Engine.Sync.foldl_add_shared</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L484">Engine.Sync.purge_apply</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.cached_items"></a>✅ <a href="../../engine/wire/NodeLaws.lean#L276">Engine.Sync.cached_items</a> · 81 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.items_foldl_key"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L222">Engine.Sync.items_foldl_key</a> · 74 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.items_foldl_mono"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L215">Engine.Sync.items_foldl_mono</a> · 72 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.items_add_mono"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L183">Engine.Sync.items_add_mono</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.items_add"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L92">Engine.Sync.items_add</a> · 69 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.RoomTree.items_add">Engine.Sync.RoomTree.items_add</a> ↪ · 66 below</li>
<li>▫️ <a href="#law-Engine.Sync.RoomTree.default_items">Engine.Sync.RoomTree.default_items</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L83">Engine.Sync.items_mk</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L156">Engine.Sync.mem_ins_keep</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.items_add">Engine.Sync.items_add</a> ↪ · 69 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L170">Engine.Sync.ins_key</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.mem_items_foldl"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L198">Engine.Sync.mem_items_foldl</a> · 71 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.items_add">Engine.Sync.items_add</a> ↪ · 69 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L139">Engine.Sync.mem_ins_of</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.keyOf_id"></a>▫️ <a href="../../engine/wire/NodeLaws.lean#L265">Engine.Sync.keyOf_id</a> · 2 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.num_inj">Engine.Sync.num_inj</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L88">Engine.Sync.items_empty</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_items"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L520">Engine.Sync.write_items</a> · 78 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 72 below</li>
<li><details><summary><a id="law-Engine.Sync.write_ix"></a>▫️ <a href="../../engine/sync/OfferLaws.lean#L484">Engine.Sync.write_ix</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L252">Engine.Sync.foldl_inv</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.have_shown_premises"></a>✅ <a href="../../engine/sync/OfferLaws.lean#L613">Engine.Sync.have_shown_premises</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/wire/NodeLaws.lean#L262">Engine.Sync.boot_cached</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L221">Engine.inv_empty</a></li>
</ul></details></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.mem_matching"></a>▫️ <a href="../../engine/core/Decl.lean#L143">Engine.mem_matching</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_sortPos"></a>▫️ <a href="../../engine/core/Decl.lean#L138">Engine.mem_sortPos</a> · 2 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.perm_sortPos">Engine.perm_sortPos</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Noise.Symbolic.clean_decHash"></a>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L436">Connection.Noise.Symbolic.clean_decHash</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L300">Connection.Noise.Symbolic.dec_some</a></li>
<li>▫️ <a href="../../engine/wire/NoiseSymbolic.lean#L128">Connection.Noise.decHash_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.WalkInv.step"></a>▫️ <a href="../../engine/core/Purge.lean#L195">Engine.WalkInv.step</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_dependents">Engine.mem_dependents</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.pushNew_spec">Engine.pushNew_spec</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Locality.lean#L21">Engine.Sync.Reach.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_ins"></a>▫️ <a href="../../engine/core/Model.lean#L44">Engine.mem_ins</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.stepS_ops"></a>▫️ <a href="../../engine/core/Proofs.lean#L568">Engine.stepS_ops</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.decideS_fields"></a>▫️ <a href="../../engine/core/Proofs.lean#L133">Engine.decideS_fields</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_indexAllS"></a>▫️ <a href="../../engine/core/Proofs.lean#L94">Engine.mem_indexAllS</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L81">Engine.indexAllS_fields</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L18">Engine.waitOnS_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.decideS_stored"></a>▫️ <a href="../../engine/core/Proofs.lean#L169">Engine.decideS_stored</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Proofs.lean#L88">Engine.indexAllS_stored</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoomTree.items_add"></a>✅ <a href="../../engine/sync/Conn.lean#L215">Engine.Sync.RoomTree.items_add</a> · 66 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.insert_canon"></a>✅ <a href="../../engine/sync/Treap.lean#L312">Engine.Sync.insert_canon</a> · 45 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.split_canon"></a>✅ <a href="../../engine/sync/Treap.lean#L207">Engine.Sync.split_canon</a> · 44 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.Sync.top_filter"></a>▫️ <a href="../../engine/sync/Treap.lean#L172">Engine.Sync.top_filter</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.top_of_max"></a>▫️ <a href="../../engine/sync/Treap.lean#L161">Engine.Sync.top_of_max</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.top_max">Engine.Sync.top_max</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Engine.Sync.Key.plt_tie">Engine.Sync.Key.plt_tie</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.top_max">Engine.Sync.top_max</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.Key.not_lt"></a>▫️ <a href="../../engine/sync/Fp.lean#L100">Engine.Sync.Key.not_lt</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Key.lt_asymm"></a>▫️ <a href="../../engine/sync/Fp.lean#L92">Engine.Sync.Key.lt_asymm</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.Key.lt_trichotomy"></a>▫️ <a href="../../engine/sync/Fp.lean#L94">Engine.Sync.Key.lt_trichotomy</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L84">Engine.Sync.Key.lt_def</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.canon_eq"></a>▫️ <a href="../../engine/sync/Treap.lean#L108">Engine.Sync.canon_eq</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.above_lt"></a>▫️ <a href="../../engine/sync/Fp.lean#L227">Engine.Sync.above_lt</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.below_lt"></a>▫️ <a href="../../engine/sync/Fp.lean#L223">Engine.Sync.below_lt</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Treap.lean#L186">Engine.Sync.filter_comm</a></li>
<li>▫️ <a href="../../engine/sync/Treap.lean#L180">Engine.Sync.filter_congr'</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_asymm">Engine.Sync.Key.lt_asymm</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trichotomy">Engine.Sync.Key.lt_trichotomy</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Engine.Sync.Key.plt_tie">Engine.Sync.Key.plt_tie</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Treap.lean#L180">Engine.Sync.filter_congr'</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.hasKey_canon-"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L206">Engine.Sync.hasKey_canon'</a> · 37 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.hasKey_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L152">Engine.Sync.hasKey_canon</a> · 36 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.canon_nil"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L148">Engine.Sync.canon_nil</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.sorted_split"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L101">Engine.Sync.sorted_split</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_asymm">Engine.Sync.Key.lt_asymm</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trichotomy">Engine.Sync.Key.lt_trichotomy</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.val_insertM"></a>✅ <a href="../../engine/sync/Treap.lean#L445">Engine.Sync.val_insertM</a> · 26 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.val_splitM"></a>✅ <a href="../../engine/sync/Treap.lean#L435">Engine.Sync.val_splitM</a> · 25 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Treap.lean#L41">Engine.Sync.val_hashM</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/sync/Treap.lean#L41">Engine.Sync.val_hashM</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.canon_perm"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L212">Engine.Sync.canon_perm</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.top_perm"></a>✅ <a href="../../engine/sync/Fp.lean#L390">Engine.Sync.top_perm</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.top_max">Engine.Sync.top_max</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Engine.Sync.Key.plt_tie">Engine.Sync.Key.plt_tie</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.toList_canon-"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L145">Engine.Sync.toList_canon'</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.toList_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L123">Engine.Sync.toList_canon</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.sorted_split">Engine.Sync.sorted_split</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ins_held"></a>▫️ <a href="../../engine/sync/Conn.lean#L164">Engine.Sync.ins_held</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_asymm">Engine.Sync.Key.lt_asymm</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ins_sorted"></a>📐 <a href="../../engine/sync/Conn.lean#L101">Engine.Sync.ins_sorted</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trans">Engine.Sync.Key.lt_trans</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_trichotomy">Engine.Sync.Key.lt_trichotomy</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L85">Engine.Sync.ins_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.untied_cons"></a>▫️ <a href="../../engine/sync/Conn.lean#L179">Engine.Sync.untied_cons</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.sorted_prio"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L254">Engine.Sync.sorted_prio</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.Key.lt_irrefl">Engine.Sync.Key.lt_irrefl</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L150">Engine.Sync.RoomTree.sorted</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L149">Engine.Sync.RoomTree.tree_eq</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L153">Engine.Sync.ins_perm</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L234">Engine.Sync.run_eq_val</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RoomTree.default_items"></a>▫️ <a href="../../engine/sync/Conn.lean#L210">Engine.Sync.RoomTree.default_items</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.canon_nil">Engine.Sync.canon_nil</a> ↪ · 6 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.top_max"></a>▫️ <a href="../../engine/sync/Fp.lean#L192">Engine.Sync.top_max</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Key.plt_irrefl"></a>▫️ <a href="../../engine/sync/Fp.lean#L127">Engine.Sync.Key.plt_irrefl</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L122">Engine.Sync.Key.plt_nat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Key.plt_trans"></a>▫️ <a href="../../engine/sync/Fp.lean#L130">Engine.Sync.Key.plt_trans</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L122">Engine.Sync.Key.plt_nat</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L172">Engine.Sync.top_none</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Key.plt_tie"></a>✅ <a href="../../engine/sync/Fp.lean#L134">Engine.Sync.Key.plt_tie</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L122">Engine.Sync.Key.plt_nat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Key.lt_irrefl"></a>▫️ <a href="../../engine/sync/Fp.lean#L86">Engine.Sync.Key.lt_irrefl</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L84">Engine.Sync.Key.lt_def</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Key.lt_trans"></a>▫️ <a href="../../engine/sync/Fp.lean#L89">Engine.Sync.Key.lt_trans</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Fp.lean#L84">Engine.Sync.Key.lt_def</a></li>
</ul></details></li>
</ul>
