# Quality proofs › Codes, pictures and discovery

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › Codes, pictures and discovery**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1346) · 🌐 world: the node's code in a World (68) · 🪜 step: a step of a wired law (63) · 📐 model: over a model (75) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2126)

<ul>
<li><details><summary><a id="law-Qr.parse_segsBits"></a>✅ <a href="../../engine/renderer/qr/SegLaws.lean#L159">Qr.parse_segsBits</a> · 21 below</summary><ul>
<li><details><summary><a id="law-Qr.readSeg_body"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L120">Qr.readSeg_body</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Qr.readAlnum_alnumBits"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L81">Qr.readAlnum_alnumBits</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Qr.alnumChr_av"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L43">Qr.alnumChr_av</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L34">Qr.alnum_table</a></li>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L20">Qr.toNat_toUInt8</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readBits_bitsOf_lt"></a>▫️ <a href="../../engine/renderer/qr/Bits.lean#L59">Qr.readBits_bitsOf_lt</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/qr/Bits.lean#L49">Qr.readBits_bitsOf</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readNum_numBits"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L52">Qr.readNum_numBits</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Qr.dig_dv"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L22">Qr.dig_dv</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L20">Qr.toNat_toUInt8</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Qr.readBits_bitsOf_lt">Qr.readBits_bitsOf_lt</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L26">Qr.dv_lt</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readBytes_bytesBits"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L100">Qr.readBytes_bytesBits</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Qr.readBits_bitsOf_lt">Qr.readBits_bitsOf_lt</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Qr.readEci_eciBits"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L111">Qr.readEci_eciBits</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Qr.readBits_bitsOf_lt">Qr.readBits_bitsOf_lt</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Qr.readBits_bitsOf_lt">Qr.readBits_bitsOf_lt</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Qr.parse_ended"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L146">Qr.parse_ended</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Qr.readSeg_length">Qr.readSeg_length</a> ↪ · 5 below</li>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Qr.readSeg_length">Qr.readSeg_length</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Qr.readBits_bitsOf_lt">Qr.readBits_bitsOf_lt</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L139">Qr.mode_lt</a></li>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L140">Qr.mode_ne</a></li>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L63">Qr.readBits_length</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.parse_dataStream"></a>✅ <a href="../../engine/renderer/qr/SegLaws.lean#L195">Qr.parse_dataStream</a> · 28 below</summary><ul>
<li>✅ <a href="#law-Qr.parse_segsBits">Qr.parse_segsBits</a> ↪ · 21 below</li>
<li><details><summary><a id="law-Qr.bytesBits_packBytes"></a>✅ <a href="../../engine/renderer/qr/Bits.lean#L116">Qr.bytesBits_packBytes</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L107">Qr.byteBits_byteOf</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.length_bytesBits"></a>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L186">Qr.length_bytesBits</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L46">Qr.bitsOf_length</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/qr/Bits.lean#L112">Qr.bytesBits_append</a></li>
<li>▫️ <a href="../../engine/renderer/qr/SegLaws.lean#L184">Qr.length_padBytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.RS.correct_sound"></a>✅ <a href="../../engine/renderer/qr/Laws.lean#L56">Qr.RS.correct_sound</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Laws.lean#L44">Qr.RS.dist_self</a></li>
<li>▫️ <a href="../../engine/renderer/qr/Laws.lean#L49">Qr.RS.syndromes_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.RS.correct_clean"></a>✅ <a href="../../engine/renderer/qr/Laws.lean#L75">Qr.RS.correct_clean</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Laws.lean#L49">Qr.RS.syndromes_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.decodeFormat_correct"></a>✅ <a href="../../engine/renderer/qr/Format.lean#L104">Qr.decodeFormat_correct</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Qr.decodeFormatData_correct"></a>▫️ <a href="../../engine/renderer/qr/Format.lean#L89">Qr.decodeFormatData_correct</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Qr.hd_triangle"></a>▫️ <a href="../../engine/renderer/qr/Format.lean#L56">Qr.hd_triangle</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L47">Qr.countP_triangle</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L64">Qr.find?_unique</a></li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L79">Qr.format_distance</a></li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L61">Qr.hd_comm</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L102">Qr.ofBits_bits</a></li>
</ul></details></li>
<li><details><summary><a id="law-Qr.decodeVersion_correct"></a>✅ <a href="../../engine/renderer/qr/Format.lean#L115">Qr.decodeVersion_correct</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Qr.hd_triangle">Qr.hd_triangle</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L64">Qr.find?_unique</a></li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L61">Qr.hd_comm</a></li>
<li>▫️ <a href="../../engine/renderer/qr/Format.lean#L83">Qr.version_distance</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.parse_text"></a>✅ <a href="../../app/community/member/invite/Proofs.lean#L327">Community.parse_text</a> · 57 below</summary><ul>
<li><details><summary><a id="law-Community.parse_code"></a>▫️ <a href="../../app/community/member/invite/Proofs.lean#L320">Community.parse_code</a> · 48 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.parse_code_eq">Community.parse_code_eq</a> ↪ · 47 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.unprefix_webLink">Community.unprefix_webLink</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.unprefix_web">Community.unprefix_web</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L239">Community.webLink_not_ws</a></li>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L235">Community.web_not_ws</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.parse_uri"></a>✅ <a href="../../app/community/member/invite/Proofs.lean#L334">Community.parse_uri</a> · 59 below</summary><ul>
<li>▫️ <a href="#law-Community.parse_code">Community.parse_code</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.unprefix_schemeLink">Community.unprefix_schemeLink</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.unprefix_scheme">Community.unprefix_scheme</a> ↪ · 2 below</li>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L241">Community.schemeLink_not_ws</a></li>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L237">Community.scheme_not_ws</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Base62.decode_encode"></a>✅ <a href="../../app/community/member/invite/Proofs.lean#L220">Community.Base62.decode_encode</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Community.Base62.bytesOf_natOf"></a>▫️ <a href="../../app/community/member/invite/Proofs.lean#L209">Community.Base62.bytesOf_natOf</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Community.Base62.peel_natOf"></a>▫️ <a href="../../app/community/member/invite/Proofs.lean#L204">Community.Base62.peel_natOf</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L189">Community.Base62.peel_foldl</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Base62.mapM_digitOf"></a>▫️ <a href="../../app/community/member/invite/Proofs.lean#L212">Community.Base62.mapM_digitOf</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L159">Community.Base62.digitOf_charOf</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L174">Community.Base62.go_lt</a></li>
<li>▫️ <a href="../../app/community/member/invite/Proofs.lean#L163">Community.Base62.ofDigits_go</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.decode_encode"></a>📐 <a href="../../engine/wire/mdns/Laws.lean#L290">Mdns.decode_encode</a> · 21 below</summary><ul>
<li><details><summary><a id="law-Mdns.record_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L255">Mdns.record_enc</a> · 18 below</summary><ul>
<li><details><summary><a id="law-Mdns.rdata_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L204">Mdns.rdata_enc</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Mdns.name_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L164">Mdns.name_enc</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Mdns.nameAt_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L139">Mdns.nameAt_enc</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Mdns.At.cons">Mdns.At.cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L59">Mdns.At.extract</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L71">Mdns.At.size</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L125">Mdns.encName_cons</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L136">Mdns.toUInt8_toNat</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L123">Mdns.wireLen_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.txtAt_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L175">Mdns.txtAt_enc</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Mdns.At.cons">Mdns.At.cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L59">Mdns.At.extract</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L71">Mdns.At.size</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L171">Mdns.encTxt_cons</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L136">Mdns.toUInt8_toNat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.u16_at"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L79">Mdns.u16_at</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Mdns.At.cons">Mdns.At.cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L76">Mdns.u8_at</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.bytes_at"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L192">Mdns.bytes_at</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L59">Mdns.At.extract</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L71">Mdns.At.size</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L69">Mdns.At.cast</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L198">Mdns.known_toNat</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Mdns.name_enc">Mdns.name_enc</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Mdns.u32_at"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L89">Mdns.u32_at</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Mdns.u16_at">Mdns.u16_at</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Mdns.u16_at">Mdns.u16_at</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L69">Mdns.At.cast</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L71">Mdns.At.size</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.question_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L244">Mdns.question_enc</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Mdns.name_enc">Mdns.name_enc</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Mdns.u16_at">Mdns.u16_at</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L69">Mdns.At.cast</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Mdns.u16_at">Mdns.u16_at</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Mdns.many_enc"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L277">Mdns.many_enc</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L69">Mdns.At.cast</a></li>
</ul></details></li>
<li><details><summary><a id="law-Mdns.decode_roundtrip"></a>📐 <a href="../../engine/wire/mdns/Laws.lean#L586">Mdns.decode_roundtrip</a> · 37 below</summary><ul>
<li>📐 <a href="#law-Mdns.decode_encode">Mdns.decode_encode</a> ↪ · 21 below</li>
<li>📐 <a href="security-proofs-hostile-input.md#law-Mdns.decode_valid">Mdns.decode_valid</a> ↪ · 17 below</li>
</ul></details></li>
<li><a id="law-Pic.fit_small"></a>✅ <a href="../../engine/renderer/pic/Laws.lean#L28">Pic.fit_small</a></li>
<li><details><summary><a id="law-Pic.fit_long"></a>✅ <a href="../../engine/renderer/pic/Laws.lean#L62">Pic.fit_long</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Pic.scaled_long"></a>▫️ <a href="../../engine/renderer/pic/Laws.lean#L56">Pic.scaled_long</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/pic/Laws.lean#L33">Pic.scaled_le</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/renderer/pic/Laws.lean#L33">Pic.scaled_le</a></li>
</ul></details></li>
<li><details><summary><a id="law-Pic.fit_le"></a>✅ <a href="../../engine/renderer/pic/Laws.lean#L41">Pic.fit_le</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/renderer/pic/Laws.lean#L33">Pic.scaled_le</a></li>
</ul></details></li>
<li><a id="law-Pic.fit_pos"></a>✅ <a href="../../engine/renderer/pic/Laws.lean#L50">Pic.fit_pos</a></li>
<li><a id="law-Pic.fit_round"></a>✅ <a href="../../engine/renderer/pic/Laws.lean#L80">Pic.fit_round</a></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Mdns.At.cons"></a>▫️ <a href="../../engine/wire/mdns/Laws.lean#L47">Mdns.At.cons</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/mdns/Laws.lean#L28">Mdns.At.append</a></li>
</ul></details></li>
</ul>
