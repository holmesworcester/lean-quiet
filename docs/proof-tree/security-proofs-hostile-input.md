# Security proofs › Hostile input

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Security proofs › Hostile input**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1035) · 🌐 world: the node's code in a World (35) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (319) · 🧪 control: a negative control (24) · ▫️ lemma: not audited (2003)

<ul>
<li><a id="law-Engine.Codec.encode_decode"></a>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li><details><summary><a id="law-Engine.Op.id_decode"></a>✅ <a href="../../engine/core/Core.lean#L93">Engine.Op.id_decode</a> · 35 below</summary><ul>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/Core.lean#L89">Engine.Op.id_bytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.distinct_of_collisionFree"></a>📐 <a href="../../engine/core/Proofs.lean#L549">Engine.distinct_of_collisionFree</a> · 36 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Codec.encode_inj"></a>▫️ <a href="../../engine/core/Codec.lean#L788">Engine.Codec.encode_inj</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/Core.lean#L89">Engine.Op.id_bytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.op_of_valid"></a>✅ <a href="../../app/community/Family.lean#L1234">Community.op_of_valid</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_inv">Engine.spec_valid_inv</a> ↪ · 2 below</li>
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
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Pic.decode_sized"></a>✅ <a href="../../engine/renderer/pic/Laws.lean#L200">Pic.decode_sized</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/pic/Laws.lean#L187">Pic.pixels_size</a></li>
</ul></details></li>
<li><details><summary><a id="law-Image.decode_sized"></a>✅ <a href="../../engine/renderer/ImageLaws.lean#L13">Image.decode_sized</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Pic.decode_sized">Pic.decode_sized</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.decode_valid"></a>📐 <a href="../../engine/wire/mdns/Laws.lean#L541">Mdns.decode_valid</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Mdns.record_valid"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L494">Mdns.record_valid</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Mdns.rdata_valid"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L425">Mdns.rdata_valid</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Mdns.name_valid"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L372">Mdns.name_valid</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Mdns.nameAt_valid"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L330">Mdns.nameAt_valid</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L326">Mdns.take_drop_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L123">Mdns.wireLen_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.txtAt_valid"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L383">Mdns.txtAt_valid</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L171">Mdns.encTxt_cons</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L326">Mdns.take_drop_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.bytes_ok"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L376">Mdns.bytes_ok</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L322">Mdns.extract_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.encName_length"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L129">Mdns.encName_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L125">Mdns.encName_cons</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L413">Mdns.known_ofNat</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Mdns.name_valid">Mdns.name_valid</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Mdns.u16_lt"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L99">Mdns.u16_lt</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L95">Mdns.u8_lt</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.question_valid"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L484">Mdns.question_valid</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Mdns.name_valid">Mdns.name_valid</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Mdns.u16_lt">Mdns.u16_lt</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L520">Mdns.many_valid</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.parse_valid"></a>✅ <a href="../../app/community/member/invite/Proofs.lean#L186">Community.parse_valid</a> · 35 below</summary><ul>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.parse_valid"></a>✅ <a href="../../engine/renderer/qr/SegLaws.lean#L337">Qr.parse_valid</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Qr.readSeg_valid"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L304">Qr.readSeg_valid</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Qr.readNum_valid"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L217">Qr.readNum_valid</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Qr.isDigit_dig"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L30">Qr.isDigit_dig</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L17">Qr.toUInt8_toNat_of_lt</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readAlnum_valid"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L252">Qr.readAlnum_valid</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L40">Qr.alnum_chr_table</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readEci_valid"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L291">Qr.readEci_valid</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L79">Qr.readBits_lt</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L79">Qr.readBits_lt</a></li>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L279">Qr.readBytes_valid</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readSeg_length"></a>▫️ <a href="../../engine/renderer/qr/Segment.lean#L230">Qr.readSeg_length</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Qr.readAlnum_length"></a>▫️ <a href="../../engine/renderer/qr/Segment.lean#L191">Qr.readAlnum_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readBytes_length"></a>▫️ <a href="../../engine/renderer/qr/Segment.lean#L208">Qr.readBytes_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readEci_length"></a>▫️ <a href="../../engine/renderer/qr/Segment.lean#L219">Qr.readEci_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readNum_length"></a>▫️ <a href="../../engine/renderer/qr/Segment.lean#L170">Qr.readNum_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.chunk_is_slice"></a>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L51">Community.chunk_is_slice</a> · 23 below</summary><ul>
<li>✅ <a href="#law-Merkle.verify_sound">Merkle.verify_sound</a> ↪ · 21 below</li>
<li>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L11">Community.check_chunk</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.verify_sound"></a>✅ <a href="../../engine/core/Merkle.lean#L479">Merkle.verify_sound</a> · 21 below</summary><ul>
<li><details><summary><a id="law-Merkle.climb_sub"></a>✅ <a href="../../engine/core/Merkle.lean#L381">Merkle.climb_sub</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L228">Merkle.nodeIn_inj</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L338">Merkle.size_climb</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L333">Merkle.size_sub</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.leafIn_ne_nodeIn"></a>▫️ <a href="../../engine/core/Merkle.lean#L233">Merkle.leafIn_ne_nodeIn</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L204">Merkle.size_tagLeaf</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L205">Merkle.size_tagNode</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L207">Merkle.tagLeaf_ne_tagNode</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.leafIn_ne_tagEmpty"></a>▫️ <a href="../../engine/core/Merkle.lean#L244">Merkle.leafIn_ne_tagEmpty</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L208">Merkle.size_be64</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L206">Merkle.size_tagEmpty</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L204">Merkle.size_tagLeaf</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.tagEmpty_ne_nodeIn"></a>▫️ <a href="../../engine/core/Merkle.lean#L239">Merkle.tagEmpty_ne_nodeIn</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L206">Merkle.size_tagEmpty</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L205">Merkle.size_tagNode</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.be64_mod"></a>▫️ <a href="../../engine/core/Merkle.lean#L217">Merkle.be64_mod</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L211">Merkle.mod_pow_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.rootIn_inj"></a>▫️ <a href="../../engine/core/Merkle.lean#L250">Merkle.rootIn_inj</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L208">Merkle.size_be64</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.verify_iff"></a>▫️ <a href="../../engine/core/Merkle.lean#L446">Merkle.verify_iff</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L197">Merkle.beq_eq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L295">Merkle.depthOf_le_iff</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L311">Merkle.getElem?_slices</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L287">Merkle.le_pow_depthOf</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L469">Merkle.leaves_hash</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.complete_assembles"></a>✅ <a href="../../engine/core/Merkle.lean#L527">Merkle.complete_assembles</a> · 25 below</summary><ul>
<li>✅ <a href="#law-Merkle.verify_sound">Merkle.verify_sound</a> ↪ · 21 below</li>
<li><details><summary><a id="law-Merkle.assemble_slices"></a>✅ <a href="../../engine/core/Merkle.lean#L327">Merkle.assemble_slices</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L318">Merkle.assemble_range</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L311">Merkle.getElem?_slices</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L303">Merkle.one_le_nChunks</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.chunk_unique"></a>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L101">Community.chunk_unique</a> · 74 below</summary><ul>
<li><details><summary><a id="law-Community.chunk_id"></a>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L85">Community.chunk_id</a> · 73 below</summary><ul>
<li><details><summary><a id="law-Community.chunk_of_attachment"></a>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L64">Community.chunk_of_attachment</a> · 46 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1185">Community.all2_cons2</a></li>
<li>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L11">Community.check_chunk</a></li>
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
<li>✅ <a href="#law-Community.op_of_valid">Community.op_of_valid</a> ↪ · 45 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>✅ <a href="#law-Community.chunk_is_slice">Community.chunk_is_slice</a> ↪ · 23 below</li>
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
</ul></details></li>
<li><details><summary><a id="law-Community.progress_exact"></a>✅ <a href="../../app/community/Proofs.lean#L522">Community.progress_exact</a> · 105 below</summary><ul>
<li>✅ <a href="#law-Community.chunk_unique">Community.chunk_unique</a> ↪ · 74 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>✅ <a href="#law-Community.chunk_of_attachment">Community.chunk_of_attachment</a> ↪ · 46 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.matching_nodup">Engine.matching_nodup</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Merkle.index_bound"></a>✅ <a href="../../engine/core/Merkle.lean#L519">Merkle.index_bound</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Merkle.verify_iff">Merkle.verify_iff</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L641">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/community/channel/message/attachment/chunk/Proofs.lean#L11">Community.check_chunk</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1405">Community.matching_also_nil</a></li>
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
<li><details><summary><a id="law-Merkle.assumptions_hold"></a>✅ <a href="../../engine/core/Merkle.lean#L593">Merkle.assumptions_hold</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Merkle.witness_spr"></a>▫️ <a href="../../engine/core/Merkle.lean#L559">Merkle.witness_spr</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L469">Merkle.leaves_hash</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L550">Merkle.size_witness</a></li>
</ul></details></li>
<li><details><summary><a id="law-Merkle.no_injective_hash"></a>📐 <a href="../../engine/core/Merkle.lean#L272">Merkle.no_injective_hash</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L260">Merkle.length_allBytes</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L264">Merkle.mem_allBytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.drain_bounded"></a>✅ <a href="../../engine/core/Budget.lean#L167">Engine.drain_bounded</a> · 56 below</summary><ul>
<li>✅ <a href="#law-Engine.step_budget">Engine.step_budget</a> ↪ · 55 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.drain_terminates"></a>✅ <a href="../../engine/core/Termination.lean#L86">Engine.drain_terminates</a> · 18 below</summary><ul>
<li><details><summary><a id="law-Engine.step_decreases"></a>▫️ <a href="../../engine/core/Termination.lean#L50">Engine.step_decreases</a> · 17 below</summary><ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.filter_lt"></a>▫️ <a href="../../engine/core/Termination.lean#L30">Engine.filter_lt</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Termination.lean#L19">Engine.filter_le</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.step_budget"></a>✅ <a href="../../engine/core/Budget.lean#L124">Engine.step_budget</a> · 55 below</summary><ul>
<li><details><summary><a id="law-Engine.waits_le"></a>▫️ <a href="../../engine/core/Budget.lean#L113">Engine.waits_le</a> · 52 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.waitsOk_reach"></a>▫️ <a href="../../engine/core/Budget.lean#L48">Engine.waitsOk_reach</a> · 11 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.mem_purgeS_waits"></a>▫️ <a href="../../engine/core/Purge.lean#L418">Engine.mem_purgeS_waits</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L79">Engine.byteArray_beq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.waitsOk_waitOnS"></a>▫️ <a href="../../engine/core/Budget.lean#L28">Engine.waitsOk_waitOnS</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.ins_nodup"></a>▫️ <a href="../../engine/core/Model.lean#L57">Engine.ins_nodup</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.nodup_length_le"></a>▫️ <a href="../../engine/core/Budget.lean#L97">Engine.nodup_length_le</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.filter_lt">Engine.filter_lt</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.filter_lt">Engine.filter_lt</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sealed_auth"></a>✅ <a href="../../app/connection/Proofs.lean#L134">Connection.sealed_auth</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Connection.openFrame_auth">Connection.openFrame_auth</a> ↪ · 2 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.openFrame_reads">Connection.openFrame_reads</a> ↪ · 2 below</li>
<li>✅ <a href="#law-Engine.Sync.sealed_unopened">Engine.Sync.sealed_unopened</a> ↪ · 2 below</li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L117">Connection.tagged_parts</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.openFrame_auth"></a>✅ <a href="../../app/connection/Proofs.lean#L83">Connection.openFrame_auth</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Connection.openFrame_run">Connection.openFrame_run</a> ↪ · 1 below</li>
</ul></details></li>
<li><a id="law-Engine.Sync.onFrame_sealed"></a>✅ <a href="../../engine/wire/NodeLaws.lean#L55">Engine.Sync.onFrame_sealed</a></li>
<li><details><summary><a id="law-Engine.Sync.sealed_unopened"></a>✅ <a href="../../engine/wire/NodeLaws.lean#L70">Engine.Sync.sealed_unopened</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>✅ <a href="../../engine/wire/NodeLaws.lean#L55">Engine.Sync.onFrame_sealed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.buffer_bounded"></a>📐 <a href="../../engine/wire/Frame.lean#L217">Engine.Sync.buffer_bounded</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.frames_kept">Engine.Sync.frames_kept</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.frames_kept"></a>✅ <a href="../../engine/wire/Frame.lean#L160">Engine.Sync.frames_kept</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.unframe_more"></a>▫️ <a href="../../engine/wire/Frame.lean#L131">Engine.Sync.unframe_more</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/Frame.lean#L109">Engine.Sync.lenAt_isSome</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/Frame.lean#L116">Engine.Sync.unframe_rest</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.frames_tooBig"></a>✅ <a href="../../engine/wire/Frame.lean#L182">Engine.Sync.frames_tooBig</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/Frame.lean#L116">Engine.Sync.unframe_rest</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.admit_bounded"></a>✅ <a href="../../engine/wire/Slots.lean#L75">Engine.Sync.admit_bounded</a></li>
<li><details><summary><a id="law-Engine.Op.decode_exact"></a>✅ <a href="../../engine/core/Core.lean#L99">Engine.Op.decode_exact</a> · 34 below</summary><ul>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Op.decode_parts"></a>✅ <a href="../../engine/core/Core.lean#L105">Engine.Op.decode_parts</a> · 37 below</summary><ul>
<li>✅ <a href="#law-Engine.Op.decode_exact">Engine.Op.decode_exact</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Engine.Codec.length_encList_bytes"></a>▫️ <a href="../../engine/core/Codec.lean#L799">Engine.Codec.length_encList_bytes</a> · 25 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.length_enc_bytes">Engine.Codec.length_enc_bytes</a> ↪ · 24 below</li>
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
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.length_enc_bytes">Engine.Codec.length_enc_bytes</a> ↪ · 24 below</li>
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
<li><details><summary><a id="law-Engine.Codec.decode_sum"></a>✅ <a href="../../engine/core/Codec.lean#L811">Engine.Codec.decode_sum</a> · 31 below</summary><ul>
<li>▫️ <a href="#law-Engine.Codec.length_encList_bytes">Engine.Codec.length_encList_bytes</a> ↪ · 25 below</li>
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
<li>✅ <a href="../../engine/core/Codec.lean#L775">Engine.Codec.encode_decode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.hold_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L59">Engine.Sync.hold_bounded</a> · 11 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.Sync.admitAsks_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L30">Engine.Sync.admitAsks_bounded</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.inserts_size"></a>📐 <a href="../../engine/sync/BoundsLaws.lean#L20">Engine.Sync.inserts_size</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.remembers_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L37">Engine.Sync.remembers_bounded</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.remember_bounded"></a>✅ <a href="../../engine/wire/WorldLaws.lean#L35">Engine.Sync.remember_bounded</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.conn_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L224">Engine.Sync.conn_bounded</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L121">Engine.Sync.recv_bounded</a> · 15 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.hold_bounded">Engine.Sync.hold_bounded</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Sync.round_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L48">Engine.Sync.round_bounded</a> · 3 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.admitAsks_bounded">Engine.Sync.admitAsks_bounded</a> ↪ · 2 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.remember_bounded">Engine.Sync.remember_bounded</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
<li>✅ <a href="../../engine/sync/BoundsLaws.lean#L68">Engine.Sync.onWant_bounded</a></li>
<li>✅ <a href="../../engine/sync/BoundsLaws.lean#L44">Engine.Sync.start_bounded</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.hold_bounded">Engine.Sync.hold_bounded</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Sync.tick_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L108">Engine.Sync.tick_bounded</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.walkN_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L81">Engine.Sync.walkN_bounded</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.expire_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L104">Engine.Sync.expire_bounded</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L184">Engine.Sync.Step.pulse_conn</a></li>
<li>✅ <a href="../../engine/sync/BoundsLaws.lean#L44">Engine.Sync.start_bounded</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L75">Engine.Sync.serveOwed_bounded</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.remembers_bounded">Engine.Sync.remembers_bounded</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.filed_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L149">Engine.Sync.filed_bounded</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L312">Engine.Sync.foldl_inv</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.round_bounded">Engine.Sync.round_bounded</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.Sync.notify_bounded"></a>✅ <a href="../../engine/sync/BoundsLaws.lean#L184">Engine.Sync.notify_bounded</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/BoundsLaws.lean#L173">Engine.Sync.give_ids</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/BoundsLaws.lean#L68">Engine.Sync.onWant_bounded</a></li>
<li>✅ <a href="../../engine/sync/BoundsLaws.lean#L44">Engine.Sync.start_bounded</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.conn_state_bounded"></a>✅ <a href="../../engine/sync/StateLaws.lean#L163">Engine.Sync.conn_state_bounded</a> · 48 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.conn_bounded">Engine.Sync.conn_bounded</a> ↪ · 27 below</li>
<li><details><summary><a id="law-Engine.Sync.extra_tick"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L92">Engine.Sync.extra_tick</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.extra_walk"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L86">Engine.Sync.extra_walk</a> · 11 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.closure_capped">Engine.Sync.closure_capped</a> ↪ · 5 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.walk_keeps">Engine.Sync.walk_keeps</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.walk_offered"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L67">Engine.Sync.walk_offered</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.extra_start"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L23">Engine.Sync.extra_start</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L33">Engine.Sync.begin_closure_bounded</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L184">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.extra_recv"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L103">Engine.Sync.extra_recv</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.extra_hold"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L48">Engine.Sync.extra_hold</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.extra_round"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L30">Engine.Sync.extra_round</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.extra_begin"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L19">Engine.Sync.extra_begin</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L33">Engine.Sync.begin_closure_bounded</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.extra_start">Engine.Sync.extra_start</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/StateLaws.lean#L57">Engine.Sync.extra_want</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.extra_filed"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L131">Engine.Sync.extra_filed</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Engine.Sync.remember_bounded">Engine.Sync.remember_bounded</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/sync/OfferLaws.lean#L312">Engine.Sync.foldl_inv</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.extra_hold">Engine.Sync.extra_hold</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.extra_serve"></a>▫️ <a href="../../engine/sync/StateLaws.lean#L62">Engine.Sync.extra_serve</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.queue_bounded"></a>▫️ <a href="../../engine/sync/ClosureLaws.lean#L25">Engine.Sync.queue_bounded</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L19">Engine.Sync.queueClosure_bounded</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.extra_round">Engine.Sync.extra_round</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.extra_start">Engine.Sync.extra_start</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/StateLaws.lean#L152">Engine.Sync.extra_give</a></li>
<li>▫️ <a href="../../engine/sync/StateLaws.lean#L57">Engine.Sync.extra_want</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.full_round_stateless"></a>✅ <a href="../../engine/sync/ClosureLaws.lean#L75">Engine.Sync.full_round_stateless</a></li>
<li><details><summary><a id="law-Engine.Sync.closure_capped"></a>✅ <a href="../../engine/sync/ClosureLaws.lean#L43">Engine.Sync.closure_capped</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.queue_bounded">Engine.Sync.queue_bounded</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/sync/ClosureLaws.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closure_complete_under_cap"></a>✅ <a href="../../engine/sync/ClosureComplete.lean#L237">Engine.Sync.closure_complete_under_cap</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.walk_complete"></a>▫️ <a href="../../engine/sync/ClosureComplete.lean#L191">Engine.Sync.walk_complete</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.visit_inv"></a>▫️ <a href="../../engine/sync/ClosureComplete.lean#L103">Engine.Sync.visit_inv</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.queue_fits"></a>▫️ <a href="../../engine/sync/ClosureComplete.lean#L45">Engine.Sync.queue_fits</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.closureIds_nodup"></a>▫️ <a href="../../engine/sync/ClosureComplete.lean#L29">Engine.Sync.closureIds_nodup</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.mem_closureIds">Engine.Sync.mem_closureIds</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ClosureComplete.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_2</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.mem_closureIds">Engine.Sync.mem_closureIds</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ClosureComplete.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_2</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.mem_slots"></a>▫️ <a href="../../engine/sync/ClosureComplete.lean#L41">Engine.Sync.mem_slots</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureComplete.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_2</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/ClosureComplete.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_2</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/ClosureComplete.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_2</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.mem_slots">Engine.Sync.mem_slots</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.honest_no_drop"></a>✅ <a href="../../engine/sync/RetryLaws.lean#L104">Engine.Sync.honest_no_drop</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.recv_no_drop"></a>✅ <a href="../../engine/sync/RetryLaws.lean#L44">Engine.Sync.recv_no_drop</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.hold_no_drop"></a>✅ <a href="../../engine/sync/RetryLaws.lean#L32">Engine.Sync.hold_no_drop</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/RetryLaws.lean#L23">Engine.Sync.round_no_drop</a></li>
<li>✅ <a href="../../engine/sync/RetryLaws.lean#L40">Engine.Sync.want_no_drop</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.hold_no_drop">Engine.Sync.hold_no_drop</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.tickGive_drop"></a>✅ <a href="../../engine/sync/RetryLaws.lean#L70">Engine.Sync.tickGive_drop</a> · 4 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.drop_iff_silent">Engine.Sync.drop_iff_silent</a> ↪ · 2 below</li>
<li>✅ <a href="../../engine/sync/NoticeState.lean#L11">Engine.Sync.give_shape</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.drop_iff_silent">Engine.Sync.drop_iff_silent</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.filedGive_no_drop"></a>✅ <a href="../../engine/sync/RetryLaws.lean#L64">Engine.Sync.filedGive_no_drop</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/NoticeState.lean#L11">Engine.Sync.give_shape</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/NoticeState.lean#L11">Engine.Sync.give_shape</a></li>
<li>✅ <a href="../../engine/sync/RetryLaws.lean#L23">Engine.Sync.round_no_drop</a></li>
<li>✅ <a href="../../engine/sync/RetryLaws.lean#L40">Engine.Sync.want_no_drop</a></li>
<li>✅ <a href="../../engine/sync/TimeLaws.lean#L14">Engine.Sync.work_no_drop</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.work_retry_bounded"></a>📐 <a href="../../engine/sync/RetryLaws.lean#L172">Engine.Sync.work_retry_bounded</a> · 47 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.retried_holds"></a>▫️ <a href="../../engine/sync/RetryLaws.lean#L150">Engine.Sync.retried_holds</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.retried_chunks"></a>▫️ <a href="../../engine/sync/RetryLaws.lean#L157">Engine.Sync.retried_chunks</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOp_want"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L482">Engine.Sync.ofOp_want</a> · 39 below</summary><ul>
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
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.retried_start"></a>▫️ <a href="../../engine/sync/RetryLaws.lean#L141">Engine.Sync.retried_start</a> · 40 below</summary><ul>
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
<li>▫️ <a href="../../engine/sync/RetryLaws.lean#L161">Engine.Sync.pieces_short</a></li>
<li>▫️ <a href="../../engine/sync/RetryLaws.lean#L138">Engine.Sync.retried_append</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onWant_authorized">Engine.Sync.onWant_authorized</a> ↪ · 2 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_blind">Engine.Sync.serveOwed_blind</a> ↪ · 9 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_budget"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L464">Engine.Sync.serveOwed_budget</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_budget"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L136">Engine.Sync.serve_budget</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L32">Engine.Sync.serve_zero</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.drop_iff_silent">Engine.Sync.drop_iff_silent</a> ↪ · 2 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.keepalive_sent">Engine.Sync.keepalive_sent</a> ↪</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.live_stays">Engine.Sync.live_stays</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.Sync.asks_expire"></a>✅ <a href="../../engine/sync/RetryLaws.lean#L129">Engine.Sync.asks_expire</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.room_independent"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L137">Engine.Sync.room_independent</a></li>
<li><a id="law-Engine.Sync.unshown_room_answered"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L131">Engine.Sync.unshown_room_answered</a></li>
<li><a id="law-Engine.Sync.uncarried_room_answered"></a>✅ <a href="../../engine/sync/TimeLaws.lean#L148">Engine.Sync.uncarried_room_answered</a></li>
<li><a id="law-Engine.Sync.purges_notified"></a>✅ <a href="../../engine/wire/CloseLaws.lean#L63">Engine.Sync.purges_notified</a></li>
<li><details><summary><a id="law-Engine.Sync.flush_notifies"></a>✅ <a href="../../engine/wire/CloseLaws.lean#L72">Engine.Sync.flush_notifies</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.close_purges">Engine.Sync.close_purges</a> ↪</li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.Sync.mem_closureIds"></a>▫️ <a href="../../engine/sync/ClosureComplete.lean#L15">Engine.Sync.mem_closureIds</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/ClosureComplete.lean#L11">Engine.Sync.instLawfulBEqByteArray_engine_2</a></li>
</ul></details></li>
</ul>
