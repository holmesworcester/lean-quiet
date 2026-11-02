# Quality proofs

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1255) · 🌐 world: the node's code in a World (68) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (290) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2191)

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
<li><details><summary><a id="law-Engine.Sync.want_sends"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L696">Engine.Sync.want_sends</a> · 84 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.ofOp_want">Engine.Sync.ofOp_want</a> ↪ · 39 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.Sync.seal_single">Engine.Sync.seal_single</a> ↪ · 32 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_body">Engine.Sync.plainFrame_body</a> ↪ · 29 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.plainFrame_head">Engine.Sync.plainFrame_head</a> ↪ · 29 below</li>
<li><details><summary><a id="law-Engine.Sync.seal_empty"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L378">Engine.Sync.seal_empty</a> · 28 below</summary><ul>
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
<li><details><summary><a id="law-Engine.Sync.serveOwed_world"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L665">Engine.Sync.serveOwed_world</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serveOwed_one"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L632">Engine.Sync.serveOwed_one</a> · 13 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_eq_run"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L607">Engine.Sync.serveOwed_eq_run</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.fetch_cons">Engine.Sync.fetch_cons</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.hot_single"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L616">Engine.Sync.hot_single</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L604">Engine.Sync.budget_world</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
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
<li><details><summary><a id="law-Engine.Sync.fresh_served"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L683">Engine.Sync.fresh_served</a> · 16 below</summary><ul>
<li>🌐 <a href="#law-Engine.Sync.serveOwed_world">Engine.Sync.serveOwed_world</a> ↪ · 14 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L500">Engine.Sync.hot_ids</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_hot"></a>🌐 <a href="../../engine/wire/WorldLaws.lean#L1503">Engine.Sync.write_hot</a> · 56 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li><details><summary><a id="law-Engine.Sync.store_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1492">Engine.Sync.store_keeps</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.fanout_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1484">Engine.Sync.fanout_keeps</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_keeps"></a>▫️ <a href="../../engine/wire/WorldLaws.lean#L1465">Engine.Sync.write_keeps</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L506">Engine.Sync.heat_hot</a></li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.onWrite_receives"></a>🌐 <a href="../../app/Proofs.lean#L3528">Connection.Execution.onWrite_receives</a> · 109 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.store_receives"></a>🌐 <a href="../../app/Proofs.lean#L3506">Connection.Execution.store_receives</a> · 71 below</summary><ul>
<li><details><summary><a id="law-Connection.Execution.write_receives"></a>🌐 <a href="../../app/Proofs.lean#L3484">Connection.Execution.write_receives</a> · 38 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.write_takes">Engine.Sync.write_takes</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Connection.Execution.write_store_tape"></a>📐 <a href="../../app/Proofs.lean#L3459">Connection.Execution.write_store_tape</a> · 7 below</summary><ul>
<li>📐 <a href="quality-proofs-sync.md#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Connection.Execution.M.forIn_reads"></a>▫️ <a href="../../app/Proofs.lean#L3450">Connection.Execution.M.forIn_reads</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Proofs.lean#L2518">Connection.Execution.M.bind_apply</a></li>
</ul></details></li>
<li>▫️ <a href="../../app/Proofs.lean#L2518">Connection.Execution.M.bind_apply</a></li>
<li>▫️ <a href="../../app/Proofs.lean#L3447">Connection.Execution.M.getOp_apply</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.NodeTape.fanout_goes">Connection.Execution.NodeTape.fanout_goes</a> ↪ · 24 below</li>
<li><details><summary><a id="law-Connection.Execution.committed_bind"></a>✅ <a href="../../app/Proofs.lean#L3499">Connection.Execution.committed_bind</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Moves.shared_retained"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L122">Engine.Sync.Moves.shared_retained</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.purge_shared">Engine.purge_shared</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.NodeTape.put_goes">Connection.Execution.NodeTape.put_goes</a> ↪ · 11 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.GoesM.forIn-">Connection.Execution.GoesM.forIn'</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.GoesM.bind-">Connection.Execution.GoesM.bind'</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Engine.Sync.Reads.goesM">Engine.Sync.Reads.goesM</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/Proofs.lean#L2824">Connection.Execution.GoesM.pure'</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L105">Engine.durable_of_room</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L78">Engine.intake_sub</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-the-engine.md#law-Connection.Execution.NodeTape.finish_goes">Connection.Execution.NodeTape.finish_goes</a> ↪ · 43 below</li>
<li>✅ <a href="#law-Connection.Execution.committed_bind">Connection.Execution.committed_bind</a> ↪ · 13 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.converge"></a>🌐 <a href="../../engine/world/Plain.lean#L203">Engine.World.Plain.converge</a> · 129 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.grows">Engine.World.Plain.grows</a> ↪ · 120 below</li>
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
<li><details><summary><a id="law-Engine.World.Plain.offline"></a>🌐 <a href="../../engine/world/Plain.lean#L215">Engine.World.Plain.offline</a> · 131 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.grows">Engine.World.Plain.grows</a> ↪ · 120 below</li>
<li><details><summary><a id="law-Engine.World.offline_of"></a>▫️ <a href="../../engine/world/Epidemic.lean#L269">Engine.World.offline_of</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.converge_of_edge">Engine.World.converge_of_edge</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L165">Engine.World.fin_max</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.want_reaches"></a>🌐 <a href="../../engine/world/Send.lean#L41">Engine.World.Plain.want_reaches</a> · 495 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.ix_covers_start">Engine.World.Plain.ix_covers_start</a> ↪ · 340 below</li>
<li>🌐 <a href="#law-Engine.World.Plain.owed_bounded_start">Engine.World.Plain.owed_bounded_start</a> ↪ · 340 below</li>
<li>🌐 <a href="#law-Engine.World.Plain.owes_queued_start">Engine.World.Plain.owes_queued_start</a> ↪ · 340 below</li>
<li><details><summary><a id="law-Engine.World.Plain.want_delivers"></a>▫️ <a href="../../engine/world/Drain.lean#L958">Engine.World.Plain.want_delivers</a> · 303 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.want_to_op">Engine.World.Plain.want_to_op</a> ↪ · 243 below</li>
<li>🌐 <a href="#law-Engine.World.Plain.drain">Engine.World.Plain.drain</a> ↪ · 195 below</li>
<li>🌐 <a href="#law-Engine.World.Plain.op_hop">Engine.World.Plain.op_hop</a> ↪ · 125 below</li>
<li><details><summary><a id="law-Engine.World.Plain.origin_src"></a>▫️ <a href="../../engine/world/Chain.lean#L64">Engine.World.Plain.origin_src</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.enter_origin"></a>▫️ <a href="../../engine/world/Chain.lean#L51">Engine.World.Plain.enter_origin</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Chain.lean#L22">Engine.World.mem_packets_src</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.sent_le_now"></a>▫️ <a href="../../engine/world/Chain.lean#L213">Engine.World.Plain.sent_le_now</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L22">Engine.World.mem_packets_src</a></li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L32">Engine.World.step_now</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Exec.now_mono">Engine.World.Exec.now_mono</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.Plain.idxOf_lt_length"></a>▫️ <a href="../../engine/world/Drain.lean#L951">Engine.World.Plain.idxOf_lt_length</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L62">Engine.World.Net.Live.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.keeps_op"></a>▫️ <a href="../../engine/world/Send.lean#L19">Engine.World.Plain.keeps_op</a> · 121 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.step_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L144">Engine.World.Plain.step_keeps</a> · 119 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.enter_moves"></a>▫️ <a href="../../engine/world/Plain.lean#L122">Engine.World.Plain.enter_moves</a> · 98 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.entry_fresh">Engine.Sync.entry_fresh</a> ↪ · 95 below</li>
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
<li>▫️ <a href="#law-Engine.World.move_keeps">Engine.World.move_keeps</a> ↪ · 13 below</li>
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
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.Plain.managed_nil">Engine.World.Plain.managed_nil</a> ↪ · 112 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.sent_le_now">Engine.World.Plain.sent_le_now</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L62">Engine.World.Net.Live.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.drain"></a>🌐 <a href="../../engine/world/Drain.lean#L847">Engine.World.Plain.drain</a> · 195 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.step_waits">Engine.World.Plain.step_waits</a> ↪ · 191 below</li>
<li><details><summary><a id="law-Engine.World.Plain.tick_moves_world"></a>▫️ <a href="../../engine/world/Drain.lean#L820">Engine.World.Plain.tick_moves_world</a> · 132 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onTick_moves">Engine.World.onTick_moves</a> ↪ · 126 below</li>
<li><details><summary><a id="law-Engine.World.Plain.enter_self_node"></a>▫️ <a href="../../engine/world/Drain.lean#L702">Engine.World.Plain.enter_self_node</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.enter_sends"></a>▫️ <a href="../../engine/world/Link.lean#L42">Engine.World.Plain.enter_sends</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Link.lean#L23">Engine.World.mem_packets</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Exec.now_mono">Engine.World.Exec.now_mono</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.want_to_op"></a>🌐 <a href="../../engine/world/Chain.lean#L279">Engine.World.Plain.want_to_op</a> · 243 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.want_hop"></a>▫️ <a href="../../engine/world/Chain.lean#L137">Engine.World.Plain.want_hop</a> · 224 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.deliver_queues">Engine.World.Plain.deliver_queues</a> ↪ · 220 below</li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L39">Engine.World.Plain.at_addr</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L106">Engine.World.Plain.deliver_now</a></li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.Plain.op_hop">Engine.World.Plain.op_hop</a> ↪ · 125 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.sent_le_now">Engine.World.Plain.sent_le_now</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.Exec.now_mono">Engine.World.Exec.now_mono</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Epidemic.lean#L62">Engine.World.Net.Live.mono</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L209">Engine.World.Plain.Net.Live.symm</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.op_hop"></a>🌐 <a href="../../engine/world/Chain.lean#L114">Engine.World.Plain.op_hop</a> · 125 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.deliver_takes">Engine.World.Plain.deliver_takes</a> ↪ · 121 below</li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L39">Engine.World.Plain.at_addr</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L106">Engine.World.Plain.deliver_now</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.write_hop"></a>🌐 <a href="../../engine/world/Chain.lean#L185">Engine.World.Plain.write_hop</a> · 86 below</summary><ul>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.Sync.write_offers_all">Engine.Sync.write_offers_all</a> ↪ · 81 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.enter_sends">Engine.World.Plain.enter_sends</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L167">Engine.World.Plain.conn_mem</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.step_waits"></a>🌐 <a href="../../engine/world/Drain.lean#L710">Engine.World.Plain.step_waits</a> · 191 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onFrame_waits"></a>▫️ <a href="../../engine/world/Drain.lean#L666">Engine.World.onFrame_waits</a> · 148 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_waits">Engine.World.onSealed_waits</a> ↪ · 143 below</li>
<li><details><summary><a id="law-Engine.World.finish_back"></a>▫️ <a href="../../engine/world/Drain.lean#L606">Engine.World.finish_back</a> · 39 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>▫️ <a href="../../engine/world/Drain.lean#L108">Engine.World.find_map_back</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.store_back"></a>▫️ <a href="../../engine/world/Drain.lean#L613">Engine.World.store_back</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L442">Engine.World.store_facts</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.World.fanout_asked"></a>▫️ <a href="../../engine/world/Asks.lean#L415">Engine.World.fanout_asked</a> · 18 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.fanout_facts">Engine.World.fanout_facts</a> ↪ · 16 below</li>
<li>▫️ <a href="#law-Engine.World.filed_shape">Engine.World.filed_shape</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.fanout_facts">Engine.World.fanout_facts</a> ↪ · 16 below</li>
<li><details><summary><a id="law-Engine.World.write_addrs"></a>▫️ <a href="../../engine/world/Hops.lean#L182">Engine.World.write_addrs</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.write_shape">Engine.World.write_shape</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.write_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L177">Engine.World.write_conns</a> · 3 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.write_shape">Engine.World.write_shape</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.write_keeps">Engine.Sync.write_keeps</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.store_keeps">Engine.Sync.store_keeps</a> ↪ · 19 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.Sync.write_keeps">Engine.Sync.write_keeps</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L39">Engine.World.Waits.same</a></li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.onTick_moves">Engine.World.onTick_moves</a> ↪ · 126 below</li>
<li><details><summary><a id="law-Engine.World.onWrite_waits"></a>▫️ <a href="../../engine/world/Drain.lean#L620">Engine.World.onWrite_waits</a> · 66 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_back">Engine.World.finish_back</a> ↪ · 39 below</li>
<li>▫️ <a href="#law-Engine.World.store_back">Engine.World.store_back</a> ↪ · 25 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_keeps">Engine.Sync.store_keeps</a> ↪ · 19 below</li>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L522">Engine.Sync.heat_managed</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L39">Engine.World.Waits.same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onClose_waits"></a>▫️ <a href="../../engine/world/Drain.lean#L632">Engine.World.onClose_waits</a> · 44 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_back">Engine.World.finish_back</a> ↪ · 39 below</li>
<li><details><summary><a id="law-Engine.World.close_conn"></a>▫️ <a href="../../engine/world/InvIx.lean#L98">Engine.World.close_conn</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvIx.lean#L78">Engine.World.find_close</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L39">Engine.World.Waits.same</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L36">Engine.World.drop_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.connect_waits"></a>▫️ <a href="../../engine/world/Drain.lean#L654">Engine.World.connect_waits</a> · 43 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_back">Engine.World.finish_back</a> ↪ · 39 below</li>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Drain.lean#L39">Engine.World.Waits.same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_node"></a>▫️ <a href="../../engine/world/Link.lean#L57">Engine.World.Plain.deliver_node</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_sends"></a>▫️ <a href="../../engine/world/Link.lean#L65">Engine.World.Plain.deliver_sends</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Link.lean#L23">Engine.World.mem_packets</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.enter_other"></a>▫️ <a href="../../engine/world/Drain.lean#L698">Engine.World.Plain.enter_other</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Plain.enter_self_node">Engine.World.Plain.enter_self_node</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.enter_sends">Engine.World.Plain.enter_sends</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/World.lean#L226">Engine.World.Exec.world_succ</a></li>
<li>▫️ <a href="../../engine/world/Chain.lean#L106">Engine.World.Plain.deliver_now</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.grows"></a>🌐 <a href="../../engine/world/Plain.lean#L193">Engine.World.Plain.grows</a> · 120 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.step_keeps">Engine.World.Plain.step_keeps</a> ↪ · 119 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.managed_nil"></a>🌐 <a href="../../engine/world/Inv.lean#L169">Engine.World.Plain.managed_nil</a> · 112 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.managed_local"></a>▫️ <a href="../../engine/world/Inv.lean#L164">Engine.World.Plain.managed_local</a> · 103 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.managed_pieces">Engine.World.Plain.managed_pieces</a> ↪ · 73 below</li>
<li><details><summary><a id="law-Engine.World.Pieces.local"></a>▫️ <a href="../../engine/world/Pieces.lean#L394">Engine.World.Pieces.local</a> · 55 below</summary><ul>
<li>✅ <a href="#law-Engine.World.onFrame_keeps">Engine.World.onFrame_keeps</a> ↪ · 40 below</li>
<li>✅ <a href="#law-Engine.World.onTick_keeps">Engine.World.onTick_keeps</a> ↪ · 20 below</li>
<li><details><summary><a id="law-Engine.World.connect_keeps"></a>▫️ <a href="../../engine/world/Pieces.lean#L206">Engine.World.connect_keeps</a> · 9 below</summary><ul>
<li><details><summary><a id="law-Engine.World.finish_keeps"></a>▫️ <a href="../../engine/world/Pieces.lean#L186">Engine.World.finish_keeps</a> · 8 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_tail">Engine.World.finish_tail</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.World.sealRetries_ok">Engine.World.sealRetries_ok</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L150">Engine.World.Ok.call</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L139">Engine.World.foldl_drop</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L160">Engine.World.keep_bind</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.World.onClose_keeps">Engine.World.onClose_keeps</a> ↪ · 9 below</li>
<li>✅ <a href="#law-Engine.World.onWrite_keeps">Engine.World.onWrite_keeps</a> ↪ · 9 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L66">Engine.World.Plain.lawful</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Local.keeps"></a>▫️ <a href="../../engine/world/Good.lean#L154">Engine.World.Local.keeps</a> · 4 below</summary><ul>
<li><details><summary><a id="law-Engine.World.step_touch"></a>▫️ <a href="../../engine/world/Good.lean#L74">Engine.World.step_touch</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.World.enter_touch"></a>▫️ <a href="../../engine/world/Good.lean#L62">Engine.World.enter_touch</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/World.lean#L99">Engine.World.upd_other</a></li>
<li>▫️ <a href="../../engine/world/World.lean#L96">Engine.World.upd_same</a></li>
</ul></details></li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.Keeps.always">Engine.World.Keeps.always</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.owes_queued_start"></a>🌐 <a href="../../engine/world/PlainGood.lean#L150">Engine.World.Plain.owes_queued_start</a> · 340 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.good_node"></a>▫️ <a href="../../engine/world/PlainGood.lean#L142">Engine.World.Plain.good_node</a> · 339 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.good_always">Engine.World.Plain.good_always</a> ↪ · 338 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.ix_covers_start"></a>🌐 <a href="../../engine/world/PlainGood.lean#L156">Engine.World.Plain.ix_covers_start</a> · 340 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.good_node">Engine.World.Plain.good_node</a> ↪ · 339 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.owed_bounded_start"></a>🌐 <a href="../../engine/world/PlainGood.lean#L162">Engine.World.Plain.owed_bounded_start</a> · 340 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.good_node">Engine.World.Plain.good_node</a> ↪ · 339 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.deliver_wants"></a>🌐 <a href="../../engine/world/Link.lean#L99">Engine.World.Plain.deliver_wants</a> · 224 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_wants">Engine.World.onSealed_wants</a> ↪ · 214 below</li>
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
<li><details><summary><a id="law-Engine.World.Plain.deliver_queues"></a>🌐 <a href="../../engine/world/Link.lean#L120">Engine.World.Plain.deliver_queues</a> · 220 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.onSealed_queues">Engine.World.onSealed_queues</a> ↪ · 210 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.onFrame_plain">Engine.World.Plain.onFrame_plain</a> ↪ · 33 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.deliver_node">Engine.World.Plain.deliver_node</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Engine.World.onSealed_wants"></a>🌐 <a href="../../engine/world/Asks.lean#L614">Engine.World.onSealed_wants</a> · 214 below</summary><ul>
<li>✅ <a href="#law-Engine.World.recv_asked">Engine.World.recv_asked</a> ↪ · 101 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recv_hold">Engine.Sync.recv_hold</a> ↪ · 51 below</li>
<li><details><summary><a id="law-Engine.World.payload_run"></a>▫️ <a href="../../engine/world/Hops.lean#L295">Engine.World.payload_run</a> · 49 below</summary><ul>
<li><details><summary><a id="law-Engine.World.apply_store"></a>▫️ <a href="../../engine/world/Hops.lean#L255">Engine.World.apply_store</a> · 40 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_one">Engine.Sync.store_one</a> ↪ · 24 below</li>
<li><details><summary><a id="law-Engine.World.store_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L230">Engine.World.store_conns</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.World.fanout_conns"></a>▫️ <a href="../../engine/world/Hops.lean#L214">Engine.World.fanout_conns</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
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
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_cases"></a>▫️ <a href="../../engine/world/Hops.lean#L91">Engine.World.recv_cases</a> · 11 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.onHold_take">Engine.Sync.onHold_take</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L695">Engine.Sync.Conn.start_drop</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L700">Engine.Sync.Conn.start_take</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Hops.lean#L154">Engine.World.conn_isSome</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.asksOf_hold"></a>▫️ <a href="../../engine/world/Asks.lean#L590">Engine.World.asksOf_hold</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.ofOp_hold">Engine.Sync.ofOp_hold</a> ↪ · 40 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_sends"></a>▫️ <a href="../../engine/world/Asks.lean#L537">Engine.World.finish_sends</a> · 45 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.Sync.seal_mem">Engine.Sync.seal_mem</a> ↪ · 35 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 33 below</li>
<li><details><summary><a id="law-Engine.World.apply_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L485">Engine.World.apply_facts</a> · 27 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Asks.lean#L473">Engine.World.conn_replace</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.World.onHold_wants">Engine.World.onHold_wants</a> ↪ · 17 below</li>
<li><details><summary><a id="law-Engine.World.heldIn_turnH"></a>▫️ <a href="../../engine/world/Asks.lean#L600">Engine.World.heldIn_turnH</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.World.turnH_some"></a>▫️ <a href="../../engine/world/Hops.lean#L75">Engine.World.turnH_some</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.World.foldl_ingestS_some"></a>▫️ <a href="../../engine/world/Plain.lean#L48">Engine.World.foldl_ingestS_some</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Plain.lean#L39">Engine.World.ingestS_some</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 11 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.apply_reads">Engine.Sync.apply_reads</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.World.serveOwed_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L522">Engine.World.serveOwed_facts</a> · 4 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.onHold_take">Engine.Sync.onHold_take</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.forIn_suffix"></a>▫️ <a href="../../engine/world/Asks.lean#L556">Engine.World.forIn_suffix</a> · 1 below</summary><ul>
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
<li>▫️ <a href="../../engine/world/Asks.lean#L596">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L593">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_queues"></a>🌐 <a href="../../engine/world/Owed.lean#L234">Engine.World.onSealed_queues</a> · 210 below</summary><ul>
<li><details><summary><a id="law-Engine.World.apply_ix"></a>▫️ <a href="../../engine/world/Owed.lean#L136">Engine.World.apply_ix</a> · 97 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 72 below</li>
<li><details><summary><a id="law-Engine.World.fanout_ix"></a>▫️ <a href="../../engine/world/Owed.lean#L128">Engine.World.fanout_ix</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.write_ix">Engine.Sync.write_ix</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.node_serve">Engine.World.node_serve</a> ↪ · 51 below</li>
<li>▫️ <a href="#law-Engine.World.payload_run">Engine.World.payload_run</a> ↪ · 49 below</li>
<li>▫️ <a href="#law-Engine.World.finish_sends">Engine.World.finish_sends</a> ↪ · 45 below</li>
<li><details><summary><a id="law-Engine.World.recv_want"></a>▫️ <a href="../../engine/world/Owed.lean#L119">Engine.World.recv_want</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.ofOp_want">Engine.Sync.ofOp_want</a> ↪ · 39 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.wantsOf_want"></a>▫️ <a href="../../engine/world/Owed.lean#L35">Engine.World.wantsOf_want</a> · 45 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.Sync.ofOp_want">Engine.Sync.ofOp_want</a> ↪ · 39 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Op.decode_bytes">Engine.Op.decode_bytes</a> ↪ · 34 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_conn"></a>▫️ <a href="../../engine/world/Owed.lean#L220">Engine.World.finish_conn</a> · 39 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>▫️ <a href="../../engine/world/Owed.lean#L205">Engine.World.find_map_owed</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.apply_facts">Engine.World.apply_facts</a> ↪ · 27 below</li>
<li>✅ <a href="#law-Engine.World.recv_owed">Engine.World.recv_owed</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.serveOwed_facts">Engine.World.serveOwed_facts</a> ↪ · 4 below</li>
<li>✅ <a href="#law-Engine.Sync.onWant_all">Engine.Sync.onWant_all</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
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
<li>▫️ <a href="../../engine/world/Asks.lean#L596">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L593">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onSealed_takes"></a>🌐 <a href="../../engine/world/Hops.lean#L346">Engine.World.onSealed_takes</a> · 113 below</summary><ul>
<li><details><summary><a id="law-Engine.World.payload_takes"></a>▫️ <a href="../../engine/world/Hops.lean#L320">Engine.World.payload_takes</a> · 91 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recv_data">Engine.Sync.recv_data</a> ↪ · 45 below</li>
<li><details><summary><a id="law-Engine.World.apply_one_held"></a>▫️ <a href="../../engine/world/Hops.lean#L286">Engine.World.apply_one_held</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.apply_store">Engine.World.apply_store</a> ↪ · 40 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.apply_takes">Engine.Sync.apply_takes</a> ↪ · 27 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.turnH_one">Engine.Sync.turnH_one</a> ↪ · 8 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.payload_run">Engine.World.payload_run</a> ↪ · 49 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_reads">Engine.Sync.finish_reads</a> ↪ · 33 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.World.turnH_one_ops"></a>▫️ <a href="../../engine/world/Hops.lean#L81">Engine.World.turnH_one_ops</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
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
<li><details><summary><a id="law-Engine.World.onSealed_waits"></a>🌐 <a href="../../engine/world/Drain.lean#L259">Engine.World.onSealed_waits</a> · 143 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.serve_moves">Engine.World.serve_moves</a> ↪ · 50 below</li>
<li>▫️ <a href="#law-Engine.World.payload_run">Engine.World.payload_run</a> ↪ · 49 below</li>
<li>▫️ <a href="#law-Engine.World.finish_sends">Engine.World.finish_sends</a> ↪ · 45 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li><details><summary><a id="law-Engine.World.apply_other_owed"></a>▫️ <a href="../../engine/world/Drain.lean#L178">Engine.World.apply_other_owed</a> · 29 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Drain.lean#L89">Engine.World.replace_other</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.apply_facts">Engine.World.apply_facts</a> ↪ · 27 below</li>
<li>▫️ <a href="#law-Engine.World.recv_cases">Engine.World.recv_cases</a> ↪ · 11 below</li>
<li>✅ <a href="#law-Engine.World.recv_appends">Engine.World.recv_appends</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Engine.World.turnH_some">Engine.World.turnH_some</a> ↪ · 10 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_reads">Engine.Sync.serveOwed_reads</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.serveOwed_facts">Engine.World.serveOwed_facts</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.Waits.append"></a>▫️ <a href="../../engine/world/Drain.lean#L34">Engine.World.Waits.append</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.serve_other"></a>▫️ <a href="../../engine/world/Drain.lean#L197">Engine.World.serve_other</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Drain.lean#L89">Engine.World.replace_other</a></li>
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
<li>▫️ <a href="../../engine/world/Drain.lean#L39">Engine.World.Waits.same</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L596">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L108">Engine.World.find_map_back</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L593">Engine.World.setAddr_addr</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onTick_moves"></a>🌐 <a href="../../engine/world/Drain.lean#L501">Engine.World.onTick_moves</a> · 126 below</summary><ul>
<li><details><summary><a id="law-Engine.World.tick_turn"></a>▫️ <a href="../../engine/world/Drain.lean#L379">Engine.World.tick_turn</a> · 109 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.serve_moves">Engine.World.serve_moves</a> ↪ · 50 below</li>
<li>▫️ <a href="#law-Engine.World.apply_other_owed">Engine.World.apply_other_owed</a> ↪ · 29 below</li>
<li><details><summary><a id="law-Engine.World.apply_retry_addrs"></a>▫️ <a href="../../engine/world/Drain.lean#L247">Engine.World.apply_retry_addrs</a> · 28 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.apply_facts">Engine.World.apply_facts</a> ↪ · 27 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.apply_facts">Engine.World.apply_facts</a> ↪ · 27 below</li>
<li><details><summary><a id="law-Engine.World.apply_managed"></a>▫️ <a href="../../engine/world/Inv.lean#L42">Engine.World.apply_managed</a> · 27 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L36">Engine.World.drop_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.tickGive_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L146">Engine.World.tickGive_q</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.World.tick_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L123">Engine.World.tick_q</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.World.ask_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L120">Engine.World.ask_q</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L752">Engine.Sync.Conn.ask_conn</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.start_q"></a>▫️ <a href="../../engine/world/InvIx.lean#L117">Engine.World.start_q</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L741">Engine.Sync.Conn.start_conn</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L496">Engine.Sync.Step.pulse_conn</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L135">Engine.World.give_q</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.tickGive_reads">Engine.Sync.tickGive_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.apply_reads">Engine.Sync.apply_reads</a> ↪ · 5 below</li>
<li><details><summary><a id="law-Engine.World.serve_facts"></a>▫️ <a href="../../engine/world/Drain.lean#L161">Engine.World.serve_facts</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.serveOwed_reads-">Engine.Sync.serveOwed_reads'</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.tickGive_take"></a>▫️ <a href="../../engine/world/Drain.lean#L133">Engine.World.tickGive_take</a> · 2 below</summary><ul>
<li>✅ <a href="../../engine/sync/Conn.lean#L498">Engine.Sync.Step.pulse_take</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L123">Engine.World.give_take</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.serve_other">Engine.World.serve_other</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L89">Engine.Sync.Acts.append_empty</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L362">Engine.World.Acts.retry_append</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L363">Engine.World.Acts.send_append</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L364">Engine.World.Acts.serve_append</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L596">Engine.World.addr_of_addrs</a></li>
<li>▫️ <a href="../../engine/world/Drain.lean#L367">Engine.World.drop_conn_none</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L22">Engine.World.serveOwed_managed</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.finish_sends">Engine.World.finish_sends</a> ↪ · 45 below</li>
<li>▫️ <a href="#law-Engine.World.finish_conn">Engine.World.finish_conn</a> ↪ · 39 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.finish_run">Engine.Sync.finish_run</a> ↪ · 37 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.World.forIn_after">Engine.World.forIn_after</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Drain.lean#L108">Engine.World.find_map_back</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L32">Engine.World.sweep_none</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.serve_moves"></a>🌐 <a href="../../engine/world/Drain.lean#L210">Engine.World.serve_moves</a> · 50 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li><details><summary><a id="law-Engine.Sync.serveOwed_pending"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L81">Engine.Sync.serveOwed_pending</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.serve_pending"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L21">Engine.Sync.serve_pending</a> · 5 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.serve_head">Engine.Sync.serve_head</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serve_cons">Engine.Sync.serve_cons</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/TimeLaws.lean#L9">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L32">Engine.Sync.serve_zero</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.fetch_all">Engine.Sync.fetch_all</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.filter_idxOf_le"></a>📐 <a href="../../engine/sync/ClosureDelivery.lean#L62">Engine.Sync.filter_idxOf_le</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/TimeLaws.lean#L9">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/TimeLaws.lean#L9">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L57">Engine.Sync.Room.notices_sync</a></li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L54">Engine.Sync.Room.syncs_sync</a></li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L60">Engine.Sync.Room.takes_sync</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L473">Engine.World.conn_replace</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onHold_wants"></a>✅ <a href="../../engine/world/Asks.lean#L173">Engine.World.onHold_wants</a> · 17 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.World.admitAsks_mem"></a>▫️ <a href="../../engine/world/Asks.lean#L101">Engine.World.admitAsks_mem</a> · 3 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Conn.has_carried_eq">Engine.Sync.Conn.has_carried_eq</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.World.chunks_want"></a>▫️ <a href="../../engine/world/Asks.lean#L112">Engine.World.chunks_want</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.chunks_cover">Engine.Sync.chunks_cover</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/Asks.lean#L118">Engine.World.wantStep_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_asked"></a>✅ <a href="../../engine/world/Asks.lean#L276">Engine.World.recv_asked</a> · 101 below</summary><ul>
<li><details><summary><a id="law-Engine.World.rbsr_asked"></a>▫️ <a href="../../engine/world/Asks.lean#L254">Engine.World.rbsr_asked</a> · 92 below</summary><ul>
<li><details><summary><a id="law-Engine.World.conn_answer_wants_le"></a>▫️ <a href="../../engine/world/Asks.lean#L236">Engine.World.conn_answer_wants_le</a> · 81 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.Index.answer_fun">Engine.Sync.Index.answer_fun</a> ↪ · 77 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L585">Engine.Sync.Conn.answer_blank</a></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L578">Engine.Sync.Conn.answer_shown</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L189">Engine.World.answer_wants_le</a></li>
</ul></details></li>
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
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.admitAsks_length">Engine.World.admitAsks_length</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.World.chunks_want">Engine.World.chunks_want</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_mem">Engine.World.foldl_insert_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_size">Engine.World.foldl_insert_size</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L761">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L741">Engine.Sync.Conn.start_conn</a></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L118">Engine.World.wantStep_fold</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_owed"></a>✅ <a href="../../engine/world/Owed.lean#L57">Engine.World.recv_owed</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.eraseDups_length_le">Engine.Sync.eraseDups_length_le</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_insert_mem">Engine.World.foldl_insert_mem</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L761">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/Conn.lean#L741">Engine.Sync.Conn.start_conn</a></li>
<li>▫️ <a href="../../engine/world/Owed.lean#L42">Engine.World.onRbsr_owed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_appends"></a>✅ <a href="../../engine/world/Drain.lean#L46">Engine.World.recv_appends</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.start_q">Engine.World.start_q</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L761">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/ServeLaws.lean#L330">Engine.Sync.onWant_order</a></li>
<li>▫️ <a href="../../engine/world/Owed.lean#L42">Engine.World.onRbsr_owed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.node_serve"></a>🌐 <a href="../../engine/world/Owed.lean#L164">Engine.World.node_serve</a> · 51 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li>✅ <a href="#law-Engine.Sync.serveOwed_hot">Engine.Sync.serveOwed_hot</a> ↪ · 6 below</li>
<li>✅ <a href="#law-Engine.Sync.serve_pending">Engine.Sync.serve_pending</a> ↪ · 5 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.has_of_mem">Engine.Sync.has_of_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
<li>▫️ <a href="../../engine/world/Asks.lean#L473">Engine.World.conn_replace</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.good_always"></a>🌐 <a href="../../engine/world/PlainGood.lean#L130">Engine.World.Plain.good_always</a> · 338 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.good_keeps">Engine.World.Plain.good_keeps</a> ↪ · 332 below</li>
<li>🌐 <a href="#law-Engine.World.Keeps.always">Engine.World.Keeps.always</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.World.Plain.good_start"></a>▫️ <a href="../../engine/world/PlainGood.lean#L116">Engine.World.Plain.good_start</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L167">Engine.Sync.held_empty_reachable</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.good_keeps"></a>🌐 <a href="../../engine/world/PlainGood.lean#L112">Engine.World.Plain.good_keeps</a> · 332 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.good_local"></a>▫️ <a href="../../engine/world/PlainGood.lean#L89">Engine.World.Plain.good_local</a> · 321 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Plain.ix_pieces">Engine.World.Plain.ix_pieces</a> ↪ · 144 below</li>
<li><details><summary><a id="law-Engine.World.Plain.settled_local"></a>▫️ <a href="../../engine/world/PlainGood.lean#L82">Engine.World.Plain.settled_local</a> · 139 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.runs_moves"></a>▫️ <a href="../../engine/world/PlainGood.lean#L61">Engine.World.Plain.runs_moves</a> · 99 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.enter_moves">Engine.World.Plain.enter_moves</a> ↪ · 98 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.connect_moves">Engine.World.Plain.connect_moves</a> ↪ · 53 below</li>
</ul></details></li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.Moves.store_settled">Engine.Sync.Moves.store_settled</a> ↪ · 66 below</li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.Plain.oq_pieces">Engine.World.Plain.oq_pieces</a> ↪ · 106 below</li>
<li><details><summary><a id="law-Engine.World.Plain.store_local"></a>▫️ <a href="../../engine/world/PlainGood.lean#L77">Engine.World.Plain.store_local</a> · 105 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.runs_moves">Engine.World.Plain.runs_moves</a> ↪ · 99 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.Moves.store_reachable">Engine.Sync.Moves.store_reachable</a> ↪ · 4 below</li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.Plain.bounded_pieces">Engine.World.Plain.bounded_pieces</a> ↪ · 103 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.managed_local">Engine.World.Plain.managed_local</a> ↪ · 103 below</li>
<li><details><summary><a id="law-Engine.World.boot_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L377">Engine.World.boot_ixinv</a> · 82 below</summary><ul>
<li><details><summary><a id="law-Engine.World.covers_foldl"></a>▫️ <a href="../../engine/world/InvIx.lean#L279">Engine.World.covers_foldl</a> · 81 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_key">Engine.Sync.items_foldl_key</a> ↪ · 74 below</li>
<li><details><summary><a id="law-Engine.World.keyed_foldl"></a>▫️ <a href="../../engine/world/InvIx.lean#L270">Engine.World.keyed_foldl</a> · 72 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.mem_items_foldl">Engine.Sync.mem_items_foldl</a> ↪ · 71 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.keyOf_id">Engine.Sync.keyOf_id</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 72 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.Pieces.local">Engine.World.Pieces.local</a> ↪ · 55 below</li>
<li>▫️ <a href="../../engine/world/Good.lean#L135">Engine.World.Local.mono</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L66">Engine.World.Plain.lawful</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.good_keeps"></a>▫️ <a href="../../engine/world/Good.lean#L210">Engine.World.good_keeps</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Local.keeps">Engine.World.Local.keeps</a> ↪ · 4 below</li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.sent_keeps">Engine.World.sent_keeps</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/world/Good.lean#L144">Engine.World.Keeps.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.moves_always"></a>🌐 <a href="../../engine/world/PlainGood.lean#L136">Engine.World.Plain.moves_always</a> · 110 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.moves_boxes"></a>▫️ <a href="../../engine/world/PlainGood.lean#L71">Engine.World.Plain.moves_boxes</a> · 100 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.runs_moves">Engine.World.Plain.runs_moves</a> ↪ · 99 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Boxes.guar"></a>▫️ <a href="../../engine/world/Good.lean#L169">Engine.World.Boxes.guar</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.step_touch">Engine.World.step_touch</a> ↪ · 3 below</li>
</ul></details></li>
<li>🌐 <a href="#law-Engine.World.Guar.always">Engine.World.Guar.always</a> ↪ · 3 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.verdicts_spec"></a>🌐 <a href="../../engine/world/PlainGood.lean#L171">Engine.World.Plain.verdicts_spec</a> · 387 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.good_node">Engine.World.Plain.good_node</a> ↪ · 339 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 56 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.agree"></a>🌐 <a href="../../engine/world/PlainGood.lean#L182">Engine.World.Plain.agree</a> · 391 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.good_node">Engine.World.Plain.good_node</a> ↪ · 339 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.order_free">Engine.order_free</a> ↪ · 66 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.sent_keeps"></a>🌐 <a href="../../engine/world/Good.lean#L241">Engine.World.sent_keeps</a> · 2 below</summary><ul>
<li><details><summary><a id="law-Engine.World.enter_sent"></a>▫️ <a href="../../engine/world/Good.lean#L230">Engine.World.enter_sent</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/Good.lean#L221">Engine.World.mem_packets_sent</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Keeps.always"></a>🌐 <a href="../../engine/world/Good.lean#L191">Engine.World.Keeps.always</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/world/World.lean#L230">Engine.World.Exec.reachable</a></li>
<li>▫️ <a href="../../engine/world/Good.lean#L184">Engine.World.Keeps.reach</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Guar.always"></a>🌐 <a href="../../engine/world/Good.lean#L197">Engine.World.Guar.always</a> · 3 below</summary><ul>
<li>🌐 <a href="#law-Engine.World.Keeps.always">Engine.World.Keeps.always</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onTick_keeps"></a>✅ <a href="../../engine/world/Pieces.lean#L382">Engine.World.onTick_keeps</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onTickReserved_keeps"></a>▫️ <a href="../../engine/world/Pieces.lean#L358">Engine.World.onTickReserved_keeps</a> · 18 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_keeps">Engine.World.finish_keeps</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.World.sweepAll_keeps"></a>▫️ <a href="../../engine/world/Pieces.lean#L346">Engine.World.sweepAll_keeps</a> · 8 below</summary><ul>
<li>▫️ <a href="../../engine/world/Pieces.lean#L49">Engine.World.Lawful.forIn_inv</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L285">Engine.World.Next.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L312">Engine.World.Next.ite</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L295">Engine.World.Next.pure</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L155">Engine.World.Ok.pure</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L317">Engine.World.ite_ok</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L300">Engine.World.sweep_ok</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L49">Engine.World.Lawful.forIn_inv</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L285">Engine.World.Next.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L295">Engine.World.Next.pure</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L150">Engine.World.Ok.call</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L220">Engine.World.refresh_bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L308">Engine.World.serve_after</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L235">Engine.World.tick_ok</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onTickDirect_keeps"></a>▫️ <a href="../../engine/world/Pieces.lean#L321">Engine.World.onTickDirect_keeps</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_keeps">Engine.World.finish_keeps</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L49">Engine.World.Lawful.forIn_inv</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L285">Engine.World.Next.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L295">Engine.World.Next.pure</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L150">Engine.World.Ok.call</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L220">Engine.World.refresh_bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L308">Engine.World.serve_after</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L235">Engine.World.tick_ok</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onFrame_keeps"></a>✅ <a href="../../engine/world/Pieces.lean#L263">Engine.World.onFrame_keeps</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Engine.World.onSealed_keeps"></a>▫️ <a href="../../engine/world/Pieces.lean#L242">Engine.World.onSealed_keeps</a> · 39 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.World.finish_keeps">Engine.World.finish_keeps</a> ↪ · 8 below</li>
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
<li>▫️ <a href="../../engine/world/Pieces.lean#L49">Engine.World.Lawful.forIn_inv</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L155">Engine.World.Ok.pure</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L227">Engine.World.recv_ok</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L220">Engine.World.refresh_bind</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.finish_keeps">Engine.World.finish_keeps</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L150">Engine.World.Ok.call</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L155">Engine.World.Ok.pure</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onWrite_keeps"></a>✅ <a href="../../engine/world/Pieces.lean#L212">Engine.World.onWrite_keeps</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_keeps">Engine.World.finish_keeps</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L144">Engine.World.Ok.bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.onClose_keeps"></a>✅ <a href="../../engine/world/Pieces.lean#L201">Engine.World.onClose_keeps</a> · 9 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.finish_keeps">Engine.World.finish_keeps</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L139">Engine.World.foldl_drop</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.oq_pieces"></a>🌐 <a href="../../engine/world/InvIx.lean#L420">Engine.World.Plain.oq_pieces</a> · 106 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.pieces"></a>▫️ <a href="../../engine/world/Inv.lean#L97">Engine.World.Plain.pieces</a> · 46 below</summary><ul>
<li><details><summary><a id="law-Engine.World.Plain.calls_keep"></a>▫️ <a href="../../engine/world/Inv.lean#L74">Engine.World.Plain.calls_keep</a> · 32 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.seal_reads">Engine.Sync.seal_reads</a> ↪ · 31 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.recv_reads">Engine.Sync.recv_reads</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.tickGive_reads">Engine.Sync.tickGive_reads</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.World.Plain.follow_ok"></a>▫️ <a href="../../engine/world/Inv.lean#L82">Engine.World.Plain.follow_ok</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.forIn_inv">Engine.Sync.forIn_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L63">Engine.Sync.HeldM.run_bind</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L32">Engine.World.sweep_none</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.store_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L227">Engine.World.store_oq</a> · 26 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L46">Engine.World.SameQ.oq</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.World.recv_owed">Engine.World.recv_owed</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.World.serve_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L235">Engine.World.serve_oq</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.World.serveOwed_oq"></a>▫️ <a href="../../engine/world/InvIx.lean#L174">Engine.World.serveOwed_oq</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.serve_rest">Engine.Sync.serve_rest</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_eq">Engine.Sync.serveOwed_eq</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.foldl_erase_mem"></a>▫️ <a href="../../engine/world/InvIx.lean#L158">Engine.World.foldl_erase_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L29">Engine.Sync.byteArray_lawfulBEq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.oq_replace"></a>▫️ <a href="../../engine/world/InvIx.lean#L70">Engine.World.oq_replace</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvIx.lean#L54">Engine.World.oq_map</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.tickGive_q">Engine.World.tickGive_q</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.World.apply_gen"></a>▫️ <a href="../../engine/world/InvIx.lean#L207">Engine.World.apply_gen</a> · 6 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.store_nil">Engine.Sync.store_nil</a> ↪ · 2 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.World.oq_drop"></a>▫️ <a href="../../engine/world/InvIx.lean#L105">Engine.World.oq_drop</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.World.oq_replace">Engine.World.oq_replace</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.oq_sent"></a>▫️ <a href="../../engine/world/InvIx.lean#L108">Engine.World.oq_sent</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvIx.lean#L54">Engine.World.oq_map</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L54">Engine.Sync.Room.syncs_sync</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L46">Engine.World.SameQ.oq</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L49">Engine.World.oq_conns</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.ix_pieces"></a>🌐 <a href="../../engine/world/InvIx.lean#L446">Engine.World.Plain.ix_pieces</a> · 144 below</summary><ul>
<li><details><summary><a id="law-Engine.World.store_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L388">Engine.World.store_ixinv</a> · 122 below</summary><ul>
<li><details><summary><a id="law-Engine.World.write_ixinv"></a>▫️ <a href="../../engine/world/InvIx.lean#L324">Engine.World.write_ixinv</a> · 97 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.covers_foldl">Engine.World.covers_foldl</a> ↪ · 81 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.items_foldl_mono">Engine.Sync.items_foldl_mono</a> ↪ · 72 below</li>
<li>▫️ <a href="#law-Engine.World.keyed_foldl">Engine.World.keyed_foldl</a> ↪ · 72 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.foldl_ingestS_isSome"></a>▫️ <a href="../../engine/world/InvIx.lean#L304">Engine.World.foldl_ingestS_isSome</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L426">Engine.Sync.foldl_fileStep</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L287">Engine.World.foldl_ingestS_ops</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.fanout_ix">Engine.World.fanout_ix</a> ↪ · 16 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.fanout_reads">Engine.Sync.fanout_reads</a> ↪ · 12 below</li>
<li>▫️ <a href="../../engine/wire/WorldLaws.lean#L304">Engine.Sync.store_run</a></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L266">Engine.World.ixinv_of_ix</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.write_ixinv">Engine.World.write_ixinv</a> ↪ · 97 below</li>
<li>▫️ <a href="#law-Engine.World.Plain.pieces">Engine.World.Plain.pieces</a> ↪ · 46 below</li>
<li>▫️ <a href="#law-Engine.World.apply_gen">Engine.World.apply_gen</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.World.serveOwed_ix"></a>▫️ <a href="../../engine/world/InvIx.lean#L400">Engine.World.serveOwed_ix</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L266">Engine.World.ixinv_of_ix</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.bounded_pieces"></a>🌐 <a href="../../engine/world/InvOwed.lean#L146">Engine.World.Plain.bounded_pieces</a> · 103 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.pieces">Engine.World.Plain.pieces</a> ↪ · 46 below</li>
<li><details><summary><a id="law-Engine.World.store_bounded"></a>▫️ <a href="../../engine/world/InvOwed.lean#L123">Engine.World.store_bounded</a> · 25 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.store_facts">Engine.World.store_facts</a> ↪ · 24 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.recv_bounded"></a>▫️ <a href="../../engine/world/InvOwed.lean#L64">Engine.World.recv_bounded</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.onHold_apply">Engine.Sync.onHold_apply</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.World.start_q">Engine.World.start_q</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/sync/Conn.lean#L761">Engine.Sync.Conn.onAsk_eq</a></li>
<li>✅ <a href="../../engine/sync/ServeLaws.lean#L351">Engine.Sync.onWant_bounded_owed</a></li>
<li>▫️ <a href="../../engine/world/Owed.lean#L42">Engine.World.onRbsr_owed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.serve_bounded"></a>▫️ <a href="../../engine/world/InvOwed.lean#L129">Engine.World.serve_bounded</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.World.serveOwed_bounded"></a>▫️ <a href="../../engine/world/InvOwed.lean#L107">Engine.World.serveOwed_bounded</a> · 7 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.serve_rest">Engine.Sync.serve_rest</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.serveOwed_run">Engine.Sync.serveOwed_run</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.bounded_replace"></a>▫️ <a href="../../engine/world/InvOwed.lean#L42">Engine.World.bounded_replace</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvOwed.lean#L24">Engine.World.bounded_map</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.tickGive_q">Engine.World.tickGive_q</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.World.apply_gen">Engine.World.apply_gen</a> ↪ · 6 below</li>
<li>▫️ <a href="#law-Engine.World.write_conns">Engine.World.write_conns</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.World.bounded_drop"></a>▫️ <a href="../../engine/world/InvOwed.lean#L50">Engine.World.bounded_drop</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.bounded_replace">Engine.World.bounded_replace</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.World.bounded_sent"></a>▫️ <a href="../../engine/world/InvOwed.lean#L53">Engine.World.bounded_sent</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/world/InvOwed.lean#L24">Engine.World.bounded_map</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.World.close_conn">Engine.World.close_conn</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/sync/Notice.lean#L54">Engine.Sync.Room.syncs_sync</a></li>
<li>▫️ <a href="../../engine/world/InvOwed.lean#L20">Engine.World.bounded_conns</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.Plain.managed_pieces"></a>🌐 <a href="../../engine/world/Inv.lean#L148">Engine.World.Plain.managed_pieces</a> · 73 below</summary><ul>
<li>▫️ <a href="#law-Engine.World.Plain.pieces">Engine.World.Plain.pieces</a> ↪ · 46 below</li>
<li>▫️ <a href="#law-Engine.World.apply_managed">Engine.World.apply_managed</a> ↪ · 27 below</li>
<li>▫️ <a href="#law-Engine.Sync.store_keeps">Engine.Sync.store_keeps</a> ↪ · 19 below</li>
<li>▫️ <a href="#law-Engine.Sync.write_keeps">Engine.Sync.write_keeps</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/world/Inv.lean#L36">Engine.World.drop_managed</a></li>
<li>▫️ <a href="../../engine/world/Inv.lean#L22">Engine.World.serveOwed_managed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.dial_mutant_unindexed"></a>🧪 <a href="../../engine/world/InvIx.lean#L524">Engine.World.dial_mutant_unindexed</a> · 11 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_ingestS_isSome">Engine.World.foldl_ingestS_isSome</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/world/InvIx.lean#L287">Engine.World.foldl_ingestS_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.answer_eq"></a>✅ <a href="../../engine/sync/Conn.lean#L377">Engine.Sync.Index.answer_eq</a> · 76 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.answerT_canon">Engine.Sync.answerT_canon</a> ↪ · 63 below</li>
<li><details><summary><a id="law-Engine.Sync.val_answerTM"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L503">Engine.Sync.val_answerTM</a> · 28 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.val_piecesTM"></a>▫️ <a href="../../engine/sync/TreapAnswer.lean#L496">Engine.Sync.val_piecesTM</a> · 27 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.val_rangeTM"></a>✅ <a href="../../engine/sync/TreapAnswer.lean#L491">Engine.Sync.val_rangeTM</a> · 26 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.Sync.val_splitM">Engine.Sync.val_splitM</a> ↪ · 25 below</li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.val_rangeTM">Engine.Sync.val_rangeTM</a> ↪ · 26 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.tree_eq"></a>▫️ <a href="../../engine/sync/Conn.lean#L272">Engine.Sync.Index.tree_eq</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.canon_nil">Engine.Sync.canon_nil</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L157">Engine.Sync.RoomTree.tree_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.sorted"></a>▫️ <a href="../../engine/sync/Conn.lean#L278">Engine.Sync.Index.sorted</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/sync/Conn.lean#L158">Engine.Sync.RoomTree.sorted</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/sync/Conn.lean#L351">Engine.Sync.Index.over_full</a></li>
<li>▫️ <a href="../../engine/sync/TreapAnswer.lean#L234">Engine.Sync.run_eq_val</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Index.opening_eq"></a>✅ <a href="../../engine/sync/Conn.lean#L368">Engine.Sync.Index.opening_eq</a> · 69 below</summary><ul>
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
<li>▫️ <a href="../../engine/sync/Conn.lean#L351">Engine.Sync.Index.over_full</a></li>
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
<li><details><summary><a id="law-Engine.World.move_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L77">Engine.World.move_keeps</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.World.turn_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L55">Engine.World.turn_keeps</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.World.foldl_ingestS_some">Engine.World.foldl_ingestS_some</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.purge_keeps"></a>▫️ <a href="../../engine/world/Plain.lean#L63">Engine.World.purge_keeps</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.fanout_facts"></a>▫️ <a href="../../engine/world/Asks.lean#L386">Engine.World.fanout_facts</a> · 16 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Sync.filed_reads">Engine.Sync.filed_reads</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.refresh_run">Engine.Sync.refresh_run</a> ↪ · 3 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.recordGiven_run">Engine.Sync.recordGiven_run</a> ↪ · 2 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.filedGive_quiet">Engine.Sync.filedGive_quiet</a> ↪ · 1 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.filed_shape"></a>▫️ <a href="../../engine/world/Asks.lean#L348">Engine.World.filed_shape</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.write_shape"></a>▫️ <a href="../../engine/world/Hops.lean#L158">Engine.World.write_shape</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.forIn_yield">Engine.Sync.forIn_yield</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.finish_tail"></a>▫️ <a href="../../engine/world/Pieces.lean#L175">Engine.World.finish_tail</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/world/Pieces.lean#L49">Engine.World.Lawful.forIn_inv</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L150">Engine.World.Ok.call</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L155">Engine.World.Ok.pure</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.World.sealRetries_ok"></a>▫️ <a href="../../engine/world/Pieces.lean#L166">Engine.World.sealRetries_ok</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/world/Pieces.lean#L49">Engine.World.Lawful.forIn_inv</a></li>
<li>▫️ <a href="../../engine/world/Pieces.lean#L160">Engine.World.keep_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Counted.cost_map"></a>▫️ <a href="../../engine/core/Cost.lean#L455">Engine.Counted.cost_map</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Cost.lean#L85">Engine.Meter.add_zero</a></li>
</ul></details></li>
</ul>
