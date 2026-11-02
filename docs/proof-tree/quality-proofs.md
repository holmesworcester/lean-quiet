# Quality proofs

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1212) · 🌐 world: the node's code in a World (46) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (290) · 🧪 control: a negative control (31) · ▫️ lemma: not audited (2105)

<ul>
<li><details><summary><a id="law-Engine.Sync.onWant_all"></a>✅ <a href="../../engine/sync/ServeLaws.lean#L311">Engine.Sync.onWant_all</a> · 3 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.seal_nil">Engine.Sync.seal_nil</a> ↪ · 28 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_world"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L622">Engine.Sync.serveOwed_world</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serveOwed_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L589">Engine.Sync.serveOwed_one</a> · 12 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Engine.Sync.write_hot"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1460">Engine.Sync.write_hot</a> · 56 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li><details><summary><a id="law-Engine.Sync.store_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1449">Engine.Sync.store_keeps</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fanout_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1441">Engine.Sync.fanout_keeps</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1422">Engine.Sync.write_keeps</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L506">Engine.Sync.heat_hot</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.onWrite_receives"></a>🌐 <a href="../../app/Proofs.lean#L3295">Connection.Execution.onWrite_receives</a> · 109 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.store_receives"></a>🌐 <a href="../../app/Proofs.lean#L3273">Connection.Execution.store_receives</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.write_receives"></a>🌐 <a href="../../app/Proofs.lean#L3251">Connection.Execution.write_receives</a> · 38 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.write_takes">Engine.Sync.write_takes</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Connection.Execution.write_store_tape"></a>📐 <a href="../../app/Proofs.lean#L3226">Connection.Execution.write_store_tape</a> · 7 below</summary><ul>
<li>📐 <a href="quality-proofs-sync.md#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.Execution.M.forIn_reads"></a>▫️ <a href="../../app/Proofs.lean#L3217">Connection.Execution.M.forIn_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L2146">Connection.Execution.M.bind_apply</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2146">Connection.Execution.M.bind_apply</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L3214">Connection.Execution.M.getOp_apply</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.NodeTape.fanout_goes">Connection.Execution.NodeTape.fanout_goes</a> ↪ · 24 below</li>
<li><details><summary><a id="law-Connection.Execution.committed_bind"></a>✅ <a href="../../app/Proofs.lean#L3266">Connection.Execution.committed_bind</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Moves.shared_retained"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L122">Engine.Sync.Moves.shared_retained</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.purge_shared">Engine.purge_shared</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.NodeTape.put_goes">Connection.Execution.NodeTape.put_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.ReadsHeld.goes">Connection.Execution.ReadsHeld.goes</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2649">Connection.Execution.GoesM.pure'</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L105">Engine.durable_of_room</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L78">Engine.intake_sub</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.apply_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L37">Engine.World.apply_managed</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L425">Engine.World.store_facts</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.fanout_asked">Engine.World.fanout_asked</a> ↪ · 18 below</li>
<li>▫️ <a href="#law-Engine.World.fanout_facts">Engine.World.fanout_facts</a> ↪ · 16 below</li>
<li>▫️ <a href="#law-Engine.World.write_addrs">Engine.World.write_addrs</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.write_keeps">Engine.Sync.write_keeps</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L31">Engine.World.drop_managed</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li>✅ <a href="../../engine/sync/Conn.lean#L485">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L287">Engine.World.give_q</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.apply_gen"></a>▫️ <a href="../../engine/world/InvIx.lean#L359">Engine.World.apply_gen</a> · 6 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li><details><summary><a id="law-Engine.World.Plain.ix_covers_start"></a>🌐 <a href="../../engine/world/InvIx.lean#L697">Engine.World.Plain.ix_covers_start</a> · 157 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.ix_covers"></a>▫️ <a href="../../engine/world/InvIx.lean#L689">Engine.World.Plain.ix_covers</a> · 156 below</summary><ul>
<li><details><summary><a id="law-Engine.World.ix_pieces"></a>▫️ <a href="../../engine/world/InvIx.lean#L599">Engine.World.ix_pieces</a> · 138 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L574">Engine.World.store_ixinv</a> · 122 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L510">Engine.World.write_ixinv</a> · 97 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.covers_foldl">Engine.World.covers_foldl</a> ↪ · 81 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 72 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 72 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_ingestS_isSome">Engine.World.foldl_ingestS_isSome</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L426">Engine.Sync.foldl_fileStep</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L473">Engine.World.foldl_ingestS_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_ix"></a>▫️ <a href="../../engine/world/Owed.lean#L128">Engine.World.fanout_ix</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.fanout_reads">Engine.Sync.fanout_reads</a> ↪ · 14 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L452">Engine.World.ixinv_of_ix</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_ixinv">Engine.World.write_ixinv</a> ↪ · 97 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li>▫️ <a href="#law-Engine.World.apply_gen">Engine.World.apply_gen</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.World.serveOwed_ix"></a>▫️ <a href="../../engine/world/InvIx.lean#L586">Engine.World.serveOwed_ix</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.finish_node">Engine.World.finish_node</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L452">Engine.World.ixinv_of_ix</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.boot_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L563">Engine.World.boot_ixinv</a> · 82 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.covers_foldl">Engine.World.covers_foldl</a> ↪ · 81 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 72 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Plain.always">Engine.World.Plain.always</a> ↪ · 56 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_wants"></a>🌐 <a href="../../engine/world/Link.lean#L99">Engine.World.Plain.deliver_wants</a> · 219 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_wants">Engine.World.onSealed_wants</a> ↪ · 209 below</li>
<li><details><summary><a id="law-Engine.World.Plain.onFrame_plain"></a>▫️ <a href="../../engine/world/Link.lean#L75">Engine.World.Plain.onFrame_plain</a> · 33 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
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
<li><details><summary><a id="law-Engine.World.Plain.deliver_queues"></a>🌐 <a href="../../engine/world/Link.lean#L120">Engine.World.Plain.deliver_queues</a> · 220 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_queues">Engine.World.onSealed_queues</a> ↪ · 210 below</li>
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
<li><details><summary><a id="law-Engine.World.onFrame_takes"></a>▫️ <a href="../../engine/world/Hops.lean#L413">Engine.World.onFrame_takes</a> · 118 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_takes">Engine.World.onSealed_takes</a> ↪ · 113 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
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
<li><details><summary><a id="law-Engine.World.onSealed_wants"></a>🌐 <a href="../../engine/world/Asks.lean#L597">Engine.World.onSealed_wants</a> · 209 below</summary><ul>
<li>✅ <a href="#law-Engine.World.recv_asked">Engine.World.recv_asked</a> ↪ · 98 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recv_hold">Engine.Sync.recv_hold</a> ↪ · 53 below</li>
<li><details><summary><a id="law-Engine.World.payload_run"></a>▫️ <a href="../../engine/world/Hops.lean#L295">Engine.World.payload_run</a> · 49 below</summary><ul>
<li><details><summary><a id="law-Engine.World.apply_store"></a>▫️ <a href="../../engine/world/Hops.lean#L255">Engine.World.apply_store</a> · 40 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_one">Engine.Sync.store_one</a> ↪ · 26 below</li>
<li><details><summary><a id="law-Engine.World.store_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L230">Engine.World.store_conns</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.World.fanout_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L214">Engine.World.fanout_conns</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.put_held"></a>▫️ <a href="../../engine/world/Hops.lean#L240">Engine.World.put_held</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_held"></a>▫️ <a href="../../engine/world/Hops.lean#L187">Engine.World.write_held</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.write_nil">Engine.Sync.write_nil</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_cases"></a>▫️ <a href="../../engine/world/Hops.lean#L91">Engine.World.recv_cases</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.onHold_take">Engine.Sync.onHold_take</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L602">Engine.Sync.Conn.start_drop</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L607">Engine.Sync.Conn.start_take</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Hops.lean#L154">Engine.World.conn_isSome</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_sends"></a>▫️ <a href="../../engine/world/Asks.lean#L520">Engine.World.finish_sends</a> · 46 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.Sync.seal_mem">Engine.Sync.seal_mem</a> ↪ · 35 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.asksOf_hold"></a>▫️ <a href="../../engine/world/Asks.lean#L573">Engine.World.asksOf_hold</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li><details><summary><a id="law-Engine.World.apply_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L468">Engine.World.apply_facts</a> · 27 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Asks.lean#L456">Engine.World.conn_replace</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.World.onHold_wants">Engine.World.onHold_wants</a> ↪ · 15 below</li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 13 below</li>
<li><details><summary><a id="law-Engine.World.heldIn_turnH"></a>▫️ <a href="../../engine/world/Asks.lean#L583">Engine.World.heldIn_turnH</a> · 11 below</summary><ul>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.apply_reads">Engine.Sync.apply_reads</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.World.serveOwed_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L505">Engine.World.serveOwed_facts</a> · 3 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.onHold_take">Engine.Sync.onHold_take</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.forIn_suffix"></a>▫️ <a href="../../engine/world/Asks.lean#L539">Engine.World.forIn_suffix</a> · 1 below</summary><ul>
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
<li>▫️ <a href="../../engine/world/Asks.lean#L579">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L576">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_queues"></a>🌐 <a href="../../engine/world/Owed.lean#L234">Engine.World.onSealed_queues</a> · 210 below</summary><ul>
<li><details><summary><a id="law-Engine.World.apply_ix"></a>▫️ <a href="../../engine/world/Owed.lean#L136">Engine.World.apply_ix</a> · 97 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 72 below</li>
<li>▫️ <a href="#law-Engine.World.fanout_ix">Engine.World.fanout_ix</a> ↪ · 16 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.write_ix">Engine.Sync.write_ix</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L261">Engine.Sync.store_run</a></li>
</ul></details></li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 38 below</li>
<li>▫️ <a href="../../engine/world/Owed.lean#L205">Engine.World.find_map_owed</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.apply_facts">Engine.World.apply_facts</a> ↪ · 27 below</li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 13 below</li>
<li>✅ <a href="#law-Engine.World.recv_owed">Engine.World.recv_owed</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Engine.Sync.onWant_all">Engine.Sync.onWant_all</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.serveOwed_facts">Engine.World.serveOwed_facts</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li>▫️ <a href="../../engine/world/Asks.lean#L579">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L576">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_takes"></a>🌐 <a href="../../engine/world/Hops.lean#L346">Engine.World.onSealed_takes</a> · 113 below</summary><ul>
<li><details><summary><a id="law-Engine.World.payload_takes"></a>▫️ <a href="../../engine/world/Hops.lean#L320">Engine.World.payload_takes</a> · 91 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recv_data">Engine.Sync.recv_data</a> ↪ · 45 below</li>
<li><details><summary><a id="law-Engine.World.apply_one_held"></a>▫️ <a href="../../engine/world/Hops.lean#L286">Engine.World.apply_one_held</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.apply_store">Engine.World.apply_store</a> ↪ · 40 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.apply_takes">Engine.Sync.apply_takes</a> ↪ · 29 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.payload_run">Engine.World.payload_run</a> ↪ · 49 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 35 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.World.turnH_one_ops"></a>▫️ <a href="../../engine/world/Hops.lean#L81">Engine.World.turnH_one_ops</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.chunks_want"></a>▫️ <a href="../../engine/world/Asks.lean#L112">Engine.World.chunks_want</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Asks.lean#L118">Engine.World.wantStep_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_asked"></a>✅ <a href="../../engine/world/Asks.lean#L259">Engine.World.recv_asked</a> · 98 below</summary><ul>
<li><details><summary><a id="law-Engine.World.rbsr_asked"></a>▫️ <a href="../../engine/world/Asks.lean#L236">Engine.World.rbsr_asked</a> · 89 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 77 below</li>
<li><details><summary><a id="law-Engine.World.admit_goal"></a>▫️ <a href="../../engine/world/Asks.lean#L220">Engine.World.admit_goal</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.World.admitAsks_length"></a>▫️ <a href="../../engine/world/Asks.lean#L88">Engine.World.admitAsks_length</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
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
<li>✅ <a href="../../engine/sync/Conn.lean#L668">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L648">Engine.Sync.Conn.start_conn</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L118">Engine.World.wantStep_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_owed"></a>✅ <a href="../../engine/world/Owed.lean#L57">Engine.World.recv_owed</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_mem">Engine.World.foldl_insert_mem</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L668">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L648">Engine.Sync.Conn.start_conn</a></li>
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
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L456">Engine.World.conn_replace</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.answer_eq"></a>✅ <a href="../../engine/sync/Conn.lean#L369">Engine.Sync.Index.answer_eq</a> · 76 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.answerT_canon">Engine.Sync.answerT_canon</a> ↪ · 63 below</li>
<li><details><summary><a id="law-Engine.Sync.val_answerTM"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L503">Engine.Sync.val_answerTM</a> · 28 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.val_piecesTM"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L496">Engine.Sync.val_piecesTM</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.val_rangeTM"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L491">Engine.Sync.val_rangeTM</a> · 26 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.val_splitM">Engine.Sync.val_splitM</a> ↪ · 25 below</li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.val_rangeTM">Engine.Sync.val_rangeTM</a> ↪ · 26 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.tree_eq"></a>▫️ <a href="../../engine/sync/Conn.lean#L264">Engine.Sync.Index.tree_eq</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.canon_nil">Engine.Sync.canon_nil</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L149">Engine.Sync.RoomTree.tree_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.sorted"></a>▫️ <a href="../../engine/sync/Conn.lean#L270">Engine.Sync.Index.sorted</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Conn.lean#L150">Engine.Sync.RoomTree.sorted</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L343">Engine.Sync.Index.over_full</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L234">Engine.Sync.run_eq_val</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.opening_eq"></a>✅ <a href="../../engine/sync/Conn.lean#L360">Engine.Sync.Index.opening_eq</a> · 69 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.openingT_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L433">Engine.Sync.openingT_canon</a> · 57 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.rangeT_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L278">Engine.Sync.rangeT_canon</a> · 46 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.split_canon">Engine.Sync.split_canon</a> ↪ · 44 below</li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L274">Engine.Sync.prio_filter</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.label_canon">Engine.Sync.label_canon</a> ↪ · 31 below</li>
<li><details><summary><a id="law-Engine.Sync.size_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L237">Engine.Sync.size_canon</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.toList_canon-">Engine.Sync.toList_canon'</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Sync.canon_sizeOk"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L82">Engine.Sync.canon_sizeOk</a> · 7 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.above_lt">Engine.Sync.above_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.below_lt">Engine.Sync.below_lt</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L79">Engine.Sync.mk_sizeOk</a></li>
<li>▫️ <a href="../../engine/sync/Fp.lean#L179">Engine.Sync.top_mem</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L47">Engine.Sync.Treap.size_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.toList_canon-">Engine.Sync.toList_canon'</a> ↪ · 11 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.sorted_prio">Engine.Sync.sorted_prio</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.val_openingTM"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L515">Engine.Sync.val_openingTM</a> · 27 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.val_rangeTM">Engine.Sync.val_rangeTM</a> ↪ · 26 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.Index.tree_eq">Engine.Sync.Index.tree_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.Sync.Index.sorted">Engine.Sync.Index.sorted</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L343">Engine.Sync.Index.over_full</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L234">Engine.Sync.run_eq_val</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.answerT_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L411">Engine.Sync.answerT_canon</a> · 63 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fp_canon"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L402">Engine.Sync.fp_canon</a> · 57 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.rangeT_canon">Engine.Sync.rangeT_canon</a> ↪ · 46 below</li>
<li>✅ <a href="#law-Engine.Sync.label_canon">Engine.Sync.label_canon</a> ↪ · 31 below</li>
<li>✅ <a href="#law-Engine.Sync.size_canon">Engine.Sync.size_canon</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.sorted_prio">Engine.Sync.sorted_prio</a> ↪ · 2 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.rangeT_canon">Engine.Sync.rangeT_canon</a> ↪ · 46 below</li>
<li><details><summary><a id="law-Engine.Sync.cutsT_canon"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L367">Engine.Sync.cutsT_canon</a> · 20 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.size_canon">Engine.Sync.size_canon</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.toList_canon-">Engine.Sync.toList_canon'</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.Sync.canon_sizeOk">Engine.Sync.canon_sizeOk</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.Treap.nth_toList"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L53">Engine.Sync.Treap.nth_toList</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L47">Engine.Sync.Treap.size_toList</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L307">Engine.Sync.pick_steps</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L361">Engine.Sync.runLen_pos</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L324">Engine.Sync.steps_eq</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.size_canon">Engine.Sync.size_canon</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.toList_canon-">Engine.Sync.toList_canon'</a> ↪ · 11 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.sorted_prio">Engine.Sync.sorted_prio</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.answerTM_hashes"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L592">Engine.Sync.answerTM_hashes</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.piecesTM_hashes"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L556">Engine.Sync.piecesTM_hashes</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.rangeTM_hashes"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L540">Engine.Sync.rangeTM_hashes</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.split_hashes"></a>✅ <a href="../../engine/sync/Treap.lean#L458">Engine.Sync.split_hashes</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.cost_hashM"></a>▫️ <a href="../../engine/sync/Treap.lean#L45">Engine.Sync.cost_hashM</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Counted.cost_map">Engine.Counted.cost_map</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Cost.lean#L142">Engine.CostT.ext'</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L87">Engine.Meter.add_assoc</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L85">Engine.Meter.add_zero</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L86">Engine.Meter.zero_add</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L85">Engine.Meter.add_zero</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.val_splitM">Engine.Sync.val_splitM</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Engine.Sync.split_height"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L527">Engine.Sync.split_height</a> · 24 below</summary><ul>
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
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.rangeTM_hashes">Engine.Sync.rangeTM_hashes</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Engine.Sync.cutsT_pieces"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L566">Engine.Sync.cutsT_pieces</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/sync/DepthLaws.lean#L288">Engine.Sync.div_ceil_mul</a></li>
<li>▫️ <a href="../../engine/sync/DepthLaws.lean#L283">Engine.Sync.pieces_len</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L361">Engine.Sync.runLen_pos</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.openingTM_hashes"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L623">Engine.Sync.openingTM_hashes</a> · 35 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.rangeTM_hashes">Engine.Sync.rangeTM_hashes</a> ↪ · 34 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.insert_hashes"></a>✅ <a href="../../engine/sync/Treap.lean#L476">Engine.Sync.insert_hashes</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.split_hashes">Engine.Sync.split_hashes</a> ↪ · 30 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.Sync.cost_hashM">Engine.Sync.cost_hashM</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.Counted.cost_map">Engine.Counted.cost_map</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L142">Engine.CostT.ext'</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L87">Engine.Meter.add_assoc</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L85">Engine.Meter.add_zero</a></li>
<li>▫️ <a href="../../engine/core/Cost.lean#L86">Engine.Meter.zero_add</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.label_canon"></a>✅ <a href="../../engine/sync/Treap.lean#L114">Engine.Sync.label_canon</a> · 31 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.lbl_eq">Engine.Sync.lbl_eq</a> ↪ · 29 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.canon_eq">Engine.Sync.canon_eq</a> ↪ · 5 below</li>
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
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.World.turn_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L55">Engine.World.turn_keeps</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_ingestS_some">Engine.World.foldl_ingestS_some</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.purge_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L63">Engine.World.purge_keeps</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_asked"></a>▫️ <a href="../../engine/world/Asks.lean#L398">Engine.World.fanout_asked</a> · 18 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.fanout_facts">Engine.World.fanout_facts</a> ↪ · 16 below</li>
<li><details><summary><a id="law-Engine.World.filed_shape"></a>▫️ <a href="../../engine/world/Asks.lean#L331">Engine.World.filed_shape</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L369">Engine.World.fanout_facts</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.write_addrs"></a>▫️ <a href="../../engine/world/Hops.lean#L182">Engine.World.write_addrs</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_shape"></a>▫️ <a href="../../engine/world/Hops.lean#L158">Engine.World.write_shape</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
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
<li>✅ <a href="../../engine/sync/Conn.lean#L659">Engine.Sync.Conn.ask_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.start_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L269">Engine.World.start_q</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L648">Engine.Sync.Conn.start_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.covers_foldl"></a>▫️ <a href="../../engine/world/InvIx.lean#L465">Engine.World.covers_foldl</a> · 81 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_key">Engine.Sync.items_foldl_key</a> ↪ · 74 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 72 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.keyOf_id">Engine.Sync.keyOf_id</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.keyed_foldl"></a>▫️ <a href="../../engine/world/InvIx.lean#L456">Engine.World.keyed_foldl</a> · 72 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.mem_items_foldl">Engine.Sync.mem_items_foldl</a> ↪ · 71 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.foldl_ingestS_isSome"></a>▫️ <a href="../../engine/world/InvIx.lean#L490">Engine.World.foldl_ingestS_isSome</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Counted.cost_map"></a>▫️ <a href="../../engine/core/Cost.lean#L455">Engine.Counted.cost_map</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L85">Engine.Meter.add_zero</a></li>
</ul></details></li>
</ul>
