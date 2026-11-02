# Quality proofs › The engine

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README's rows cite under **Quality proofs › The engine**. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1273) · 🌐 world: the node's code in a World (70) · 🪜 step: a step of a wired law (0) · 📐 model: over a model (305) · 🧪 control: a negative control (32) · ▫️ lemma: not audited (2292)

<ul>
<li><details><summary><a id="law-Engine.same_ops_same_verdicts"></a>✅ <a href="../../engine/core/Termination.lean#L122">Engine.same_ops_same_verdicts</a> · 74 below</summary><ul>
<li>✅ <a href="#law-Engine.order_free">Engine.order_free</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.order_free"></a>✅ <a href="../../engine/core/Proofs.lean#L671">Engine.order_free</a> · 68 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li><details><summary><a id="law-Engine.ops_eq_of_same"></a>▫️ <a href="../../engine/core/Proofs.lean#L651">Engine.ops_eq_of_same</a> · 13 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.status_eq_of_ops"></a>▫️ <a href="../../engine/core/Proofs.lean#L496">Engine.status_eq_of_ops</a> · 10 below</summary><ul>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Engine.reach_drain"></a>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
<li><details><summary><a id="law-Engine.drain_settles"></a>✅ <a href="../../engine/core/Termination.lean#L112">Engine.drain_settles</a> · 71 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.status_iff_spec"></a>✅ <a href="../../engine/core/Proofs.lean#L484">Engine.status_iff_spec</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.undecided_spec"></a>▫️ <a href="../../engine/core/Proofs.lean#L454">Engine.undecided_spec</a> · 7 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.specAt_det">Engine.specAt_det</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.spec_extends"></a>📐 <a href="../../engine/core/SpecLemmas.lean#L138">Engine.spec_extends</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_extends"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L119">Engine.specAt_extends</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.inv_ingest"></a>✅ <a href="../../engine/core/Proofs.lean#L229">Engine.inv_ingest</a> · 8 below</summary><ul>
<li>📐 <a href="#law-Engine.spec_extends">Engine.spec_extends</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_ins">Engine.mem_ins</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.inv_step"></a>✅ <a href="../../engine/core/Proofs.lean#L260">Engine.inv_step</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.spec_of_judge"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L169">Engine.spec_of_judge</a> · 7 below</summary><ul>
<li><details><summary><a id="law-Engine.common_depth"></a>▫️ <a href="../../engine/core/SpecLemmas.lean#L143">Engine.common_depth</a> · 6 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.specAt_le">Engine.specAt_le</a> ↪ · 5 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.decideS_nodup"></a>▫️ <a href="../../engine/core/Proofs.lean#L176">Engine.decideS_nodup</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.indexAllS_nodup"></a>▫️ <a href="../../engine/core/Proofs.lean#L120">Engine.indexAllS_nodup</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.ins_nodup">Engine.ins_nodup</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.mem_waitOnS">Engine.mem_waitOnS</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_stored">Engine.decideS_stored</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L30">Engine.waitOnS_idx</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L18">Engine.waitOnS_ops</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L26">Engine.waitOnS_queue</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L34">Engine.waitOnS_stored</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.production_step_waiting"></a>📐 <a href="../../app/Proofs.lean#L2749">Connection.Execution.production_step_waiting</a> · 236 below</summary><ul>
<li>📐 <a href="security-proofs-connections.md#law-Connection.Execution.production_step_moves">Connection.Execution.production_step_moves</a> ↪ · 136 below</li>
<li>✅ <a href="#law-Engine.Sync.Moves.store_waiting">Engine.Sync.Moves.store_waiting</a> ↪ · 98 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Moves.store_waiting"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L134">Engine.Sync.Moves.store_waiting</a> · 98 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.turn_waiting_held"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L193">Engine.Sync.turn_waiting_held</a> · 86 below</summary><ul>
<li>✅ <a href="#law-Engine.turn_waiting">Engine.turn_waiting</a> ↪ · 85 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.purge_waiting_held"></a>✅ <a href="../../engine/sync/StoreEvolution.lean#L97">Engine.Sync.purge_waiting_held</a> · 81 below</summary><ul>
<li>✅ <a href="#law-Engine.purge_waiting">Engine.purge_waiting</a> ↪ · 80 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.Moves.store_reachable">Engine.Sync.Moves.store_reachable</a> ↪ · 10 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.turn_waiting"></a>✅ <a href="../../engine/core/TurnLaws.lean#L446">Engine.turn_waiting</a> · 85 below</summary><ul>
<li><details><summary><a id="law-Engine.urgentClose_waiting"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L305">Engine.urgentClose_waiting</a> · 73 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.waitsOk_reach">Engine.waitsOk_reach</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.but_judgeAhead"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L219">Engine.but_judgeAhead</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.but_decide"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L176">Engine.but_decide</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.but_waitOn"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L166">Engine.but_waitOn</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.mem_waitOnS">Engine.mem_waitOnS</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L18">Engine.waitOnS_ops</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-hostile-input.md#law-Engine.mem_waitOnS">Engine.mem_waitOnS</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L203">Engine.but_drop</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L18">Engine.waitOnS_ops</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.undecided_decide"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L285">Engine.undecided_decide</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_stored">Engine.decideS_stored</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.filter_lt">Engine.filter_lt</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.waits_le_stored"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L299">Engine.waits_le_stored</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.nodup_length_le">Engine.nodup_length_le</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.undecided_waitOn"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L296">Engine.undecided_waitOn</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Proofs.lean#L22">Engine.waitOnS_status</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L34">Engine.waitOnS_stored</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_stored">Engine.decideS_stored</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.reach_judgeAhead">Engine.reach_judgeAhead</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L34">Engine.waitOnS_stored</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.but_judgeJob"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L261">Engine.but_judgeJob</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Engine.but_judgeAhead">Engine.but_judgeAhead</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L161">Engine.UrgentWaitingBut.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.waiting_drain"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L434">Engine.waiting_drain</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.waiting_step"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L391">Engine.waiting_step</a> · 11 below</summary><ul>
<li>▫️ <a href="#law-Engine.but_waitOn">Engine.but_waitOn</a> ↪ · 5 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
<li><details><summary><a id="law-Engine.UrgentClosed.req"></a>▫️ <a href="../../engine/core/Urgent.lean#L36">Engine.UrgentClosed.req</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Locality.lean#L21">Engine.Sync.Reach.trans</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.but_ingests"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L375">Engine.but_ingests</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.but_ingest"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L352">Engine.but_ingest</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L341">Engine.closed_of_extends</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L161">Engine.UrgentWaitingBut.mono</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.reach_judgeJob">Engine.reach_judgeJob</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L161">Engine.UrgentWaitingBut.mono</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L131">Engine.reach_ingests</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L441">Engine.undecided_le</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.urgent_spec"></a>✅ <a href="../../engine/core/Urgent.lean#L49">Engine.urgent_spec</a> · 10 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.UrgentClosed.req">Engine.UrgentClosed.req</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.spec_eventually"></a>✅ <a href="../../engine/core/CarryLaws.lean#L439">Engine.spec_eventually</a> · 51 below</summary><ul>
<li><details><summary><a id="law-Engine.ready_decides"></a>📐 <a href="../../engine/core/CarryLaws.lean#L403">Engine.ready_decides</a> · 36 below</summary><ul>
<li><details><summary><a id="law-Engine.ready_run"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L389">Engine.ready_run</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.ready_turn"></a>📐 <a href="../../engine/core/CarryLaws.lean#L282">Engine.ready_turn</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Engine.ready_drain_lt"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L260">Engine.ready_drain_lt</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.ready_drain">Engine.ready_drain</a> ↪ · 21 below</li>
<li>▫️ <a href="#law-Engine.ready_step">Engine.ready_step</a> ↪ · 20 below</li>
<li>▫️ <a href="#law-Engine.grows_drain">Engine.grows_drain</a> ↪ · 14 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L70">Engine.Grows.isSome</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ready_judgeJob"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L211">Engine.ready_judgeJob</a> · 23 below</summary><ul>
<li>▫️ <a href="#law-Engine.ready_judgeAhead">Engine.ready_judgeAhead</a> ↪ · 21 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ready_urgentClose"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L220">Engine.ready_urgentClose</a> · 23 below</summary><ul>
<li>▫️ <a href="#law-Engine.ready_judgeAhead">Engine.ready_judgeAhead</a> ↪ · 21 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.ready_drain">Engine.ready_drain</a> ↪ · 21 below</li>
<li><details><summary><a id="law-Engine.ready_ingests"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L230">Engine.ready_ingests</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.ready_extend">Engine.ready_extend</a> ↪ · 7 below</li>
<li>▫️ <a href="#law-Engine.grows_ingest">Engine.grows_ingest</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L103">Engine.ingest_queue</a></li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.ready_turn">Engine.ready_turn</a> ↪ · 33 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L41">Engine.rank_zero</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.grows_run"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L384">Engine.grows_run</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.TurnStep.grows"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L379">Engine.TurnStep.grows</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.grows_turn"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L302">Engine.grows_turn</a> · 18 below</summary><ul>
<li>▫️ <a href="#law-Engine.grows_drain">Engine.grows_drain</a> ↪ · 14 below</li>
<li><details><summary><a id="law-Engine.grows_judgeAhead"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L206">Engine.grows_judgeAhead</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.stepS_pop">Engine.stepS_pop</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L96">Engine.judgeAheadS_eq</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.grows_ingest">Engine.grows_ingest</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li>📐 <a href="quality-proofs-sync.md#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Locality.lean#L21">Engine.Sync.Reach.trans</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L425">Engine.eventually_all</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.closure_delivered"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L232">Engine.Sync.closure_delivered</a> · 184 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.receives"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L323">Engine.Sync.ReceiverRun.receives</a> · 96 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.invariant"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L277">Engine.Sync.ReceiverRun.invariant</a> · 72 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.store_reachable"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L268">Engine.Sync.ReceiverRun.store_reachable</a> · 13 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_reachable"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L202">Engine.Sync.write_reachable</a> · 12 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.turn_reachable">Engine.Sync.turn_reachable</a> ↪ · 7 below</li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.turn_reachable">Engine.Sync.turn_reachable</a> ↪ · 7 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_takes"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L118">Engine.Sync.write_takes</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_preserves_op"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L104">Engine.Sync.write_preserves_op</a> · 19 below</summary><ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.turnCappedS_ops">Engine.turnCappedS_ops</a> ↪ · 12 below</li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L300">Engine.Sync.foldl_ingest_keep</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L434">Engine.Sync.turn_apply</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.foldl_ingest_new">Engine.Sync.foldl_ingest_new</a> ↪ · 12 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.turnCappedS_ops">Engine.turnCappedS_ops</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.Sync.absentFold_covers"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L88">Engine.Sync.absentFold_covers</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.absentFold_keeps"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L69">Engine.Sync.absentFold_keeps</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/sync/ClosureStore.lean#L49">Engine.Sync.absentStep_keeps</a></li>
</ul></details></li>
<li>📐 <a href="../../engine/sync/ClosureStore.lean#L49">Engine.Sync.absentStep_keeps</a></li>
<li>▫️ <a href="../../engine/sync/ServeLaws.lean#L271">Engine.Sync.instLawfulBEqByteArray_engine</a></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li><details><summary><a id="law-Engine.Sync.absentFold_source"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L75">Engine.Sync.absentFold_source</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/sync/ClosureStore.lean#L58">Engine.Sync.absentStep_source</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.absentOf_new">Engine.Sync.absentOf_new</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.store_reachable">Engine.Sync.ReceiverRun.store_reachable</a> ↪ · 13 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L78">Engine.intake_sub</a></li>
<li>✅ <a href="../../engine/core/Sync.lean#L86">Engine.mem_intake_shared</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ReceiverRun.invariant">Engine.Sync.ReceiverRun.invariant</a> ↪ · 72 below</li>
<li>✅ <a href="#law-Engine.spec_eventually">Engine.spec_eventually</a> ↪ · 51 below</li>
<li>✅ <a href="also-cited.md#law-Engine.Sync.ServiceRun.eventually_emitted">Engine.Sync.ServiceRun.eventually_emitted</a> ↪ · 46 below</li>
<li><details><summary><a id="law-Engine.Sync.finite_eventually_held"></a>📐 <a href="../../engine/sync/ClosureDelivery.lean#L203">Engine.Sync.finite_eventually_held</a> · 22 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.retains"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L314">Engine.Sync.ReceiverRun.retains</a> · 21 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.keeps"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L306">Engine.Sync.ReceiverRun.keeps</a> · 20 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.write_preserves_op">Engine.Sync.write_preserves_op</a> ↪ · 19 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.turnCappedS_ops">Engine.turnCappedS_ops</a> ↪ · 12 below</li>
</ul></details></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ReceiverRun.step"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L292">Engine.Sync.ReceiverRun.step</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.write_step"></a>✅ <a href="../../engine/sync/ClosureStore.lean#L233">Engine.Sync.write_step</a> · 5 below</summary><ul>
<li>📐 <a href="#law-Engine.Sync.write_store">Engine.Sync.write_store</a> ↪ · 3 below</li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L199">Engine.Sync.turn_step</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L199">Engine.Sync.turn_step</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L299">Engine.Sync.ReceiverRun.turnsRecur</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L594">Engine.drainCap_pos</a></li>
</ul></details></li>
<li><a id="law-Engine.ingestS_known"></a>✅ <a href="../../engine/core/IdemLaws.lean#L23">Engine.ingestS_known</a></li>
<li><details><summary><a id="law-Engine.ingestS_twice"></a>✅ <a href="../../engine/core/IdemLaws.lean#L45">Engine.ingestS_twice</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/IdemLaws.lean#L27">Engine.ingestS_holds</a></li>
<li>✅ <a href="../../engine/core/IdemLaws.lean#L23">Engine.ingestS_known</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ingest_twice"></a>✅ <a href="../../engine/core/IdemLaws.lean#L50">Engine.ingest_twice</a> · 4 below</summary><ul>
<li>✅ <a href="#law-Engine.ingestS_twice">Engine.ingestS_twice</a> ↪ · 2 below</li>
<li>✅ <a href="../../engine/core/Run.lean#L112">Engine.run_ingest</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.run_ingestEach"></a>✅ <a href="../../engine/core/IdemLaws.lean#L74">Engine.run_ingestEach</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Run.lean#L112">Engine.run_ingest</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ingestAll_again"></a>✅ <a href="../../engine/core/IdemLaws.lean#L83">Engine.ingestAll_again</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.ingestAll_mem"></a>▫️ <a href="../../engine/core/IdemLaws.lean#L64">Engine.ingestAll_mem</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.ingestAll_holds"></a>▫️ <a href="../../engine/core/IdemLaws.lean#L57">Engine.ingestAll_holds</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/IdemLaws.lean#L34">Engine.ingestS_keeps</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/IdemLaws.lean#L27">Engine.ingestS_holds</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/core/IdemLaws.lean#L23">Engine.ingestS_known</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_gone"></a>✅ <a href="../../engine/core/Purge.lean#L567">Engine.purge_gone</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.mem_purgeS_idx"></a>▫️ <a href="../../engine/core/Purge.lean#L434">Engine.mem_purgeS_idx</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.purgeSet_closeUp"></a>▫️ <a href="../../engine/core/Purge.lean#L388">Engine.purgeSet_closeUp</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_shared"></a>✅ <a href="../../engine/core/Purge.lean#L580">Engine.purge_shared</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_settles"></a>✅ <a href="../../engine/core/Budget.lean#L200">Engine.purge_settles</a> · 108 below</summary><ul>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_bounded">Engine.drain_bounded</a> ↪ · 57 below</li>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.drainS_ops">Engine.drainS_ops</a> ↪ · 7 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.run_purge"></a>✅ <a href="../../engine/core/Purge.lean#L555">Engine.run_purge</a> · 19 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_walk">Engine.closeUp_walk</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.deleteAllS_eq"></a>▫️ <a href="../../engine/core/Purge.lean#L523">Engine.deleteAllS_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L501">Engine.filter_has_nil</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L498">Engine.not_has_cons</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.undecideAllS_eq"></a>▫️ <a href="../../engine/core/Purge.lean#L504">Engine.undecideAllS_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Purge.lean#L501">Engine.filter_has_nil</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L498">Engine.not_has_cons</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L492">Engine.run_deleteAll</a></li>
<li>▫️ <a href="../../engine/core/Run.lean#L72">Engine.run_pushAll</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L452">Engine.run_unsettle</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L166">Engine.run_walkDeps</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_waiting"></a>✅ <a href="../../engine/core/TurnLaws.lean#L701">Engine.purge_waiting</a> · 80 below</summary><ul>
<li>▫️ <a href="#law-Engine.urgentClose_waiting">Engine.urgentClose_waiting</a> ↪ · 73 below</li>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li><details><summary><a id="law-Engine.but_purge"></a>✅ <a href="../../engine/core/TurnLaws.lean#L674">Engine.but_purge</a> · 23 below</summary><ul>
<li><details><summary><a id="law-Engine.reach_purgeS"></a>▫️ <a href="../../engine/core/TurnLaws.lean#L658">Engine.reach_purgeS</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.closeUp_dependents"></a>▫️ <a href="../../engine/core/Proofs.lean#L360">Engine.closeUp_dependents</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_closed">Engine.closeUp_closed</a> ↪ · 11 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.purgeSet_closeUp">Engine.purgeSet_closeUp</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.mem_purgeS_waits">Engine.mem_purgeS_waits</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.purgeS_status_not"></a>▫️ <a href="../../engine/core/Purge.lean#L408">Engine.purgeS_status_not</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.purgeSet_closeUp">Engine.purgeSet_closeUp</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L375">Engine.mem_rejudgeSet_iff</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.waiting_drain">Engine.waiting_drain</a> ↪ · 12 below</li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L441">Engine.undecided_le</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.run_purgeCapped"></a>✅ <a href="../../engine/core/TurnLaws.lean#L634">Engine.run_purgeCapped</a> · 30 below</summary><ul>
<li>✅ <a href="#law-Engine.run_purge">Engine.run_purge</a> ↪ · 19 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.run_drain">Engine.run_drain</a> ↪ · 8 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.run_urgentClose">Engine.run_urgentClose</a> ↪ · 6 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.purge_named">Engine.purge_named</a> ↪ · 18 below</li>
<li><details><summary><a id="law-Engine.purge_undecides"></a>✅ <a href="../../engine/core/Proofs.lean#L380">Engine.purge_undecides</a> · 23 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_dependents">Engine.closeUp_dependents</a> ↪ · 12 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_sub">Engine.closeUp_sub</a> ↪ · 11 below</li>
<li>✅ <a href="#law-Engine.purge_shared">Engine.purge_shared</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.mem_purgeS_idx">Engine.mem_purgeS_idx</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.mem_purgeS_queue"></a>▫️ <a href="../../engine/core/Purge.lean#L428">Engine.mem_purgeS_queue</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purgeS_status_mem"></a>▫️ <a href="../../engine/core/Purge.lean#L403">Engine.purgeS_status_mem</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L375">Engine.mem_rejudgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.purge_inv"></a>✅ <a href="../../engine/core/Proofs.lean#L395">Engine.purge_inv</a> · 34 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_dependents">Engine.closeUp_dependents</a> ↪ · 12 below</li>
<li>📐 <a href="quality-proofs-sync.md#law-Engine.Sync.spec_local">Engine.Sync.spec_local</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.mem_purgeS_waits">Engine.mem_purgeS_waits</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Engine.mem_purgeS_idx">Engine.mem_purgeS_idx</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.mem_purgeS_queue">Engine.mem_purgeS_queue</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.mem_purgeS_stored"></a>▫️ <a href="../../engine/core/Purge.lean#L413">Engine.mem_purgeS_stored</a> · 2 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.purgeS_status_mem">Engine.purgeS_status_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.purgeS_status_not">Engine.purgeS_status_not</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Engine.purgeSet_closeUp">Engine.purgeSet_closeUp</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L375">Engine.mem_rejudgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_inv"></a>✅ <a href="../../engine/core/Proofs.lean#L535">Engine.reach_inv</a> · 57 below</summary><ul>
<li>✅ <a href="#law-Engine.purge_inv">Engine.purge_inv</a> ↪ · 34 below</li>
<li>✅ <a href="#law-Engine.inv_step">Engine.inv_step</a> ↪ · 24 below</li>
<li>✅ <a href="#law-Engine.inv_ingest">Engine.inv_ingest</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L221">Engine.inv_empty</a></li>
<li>▫️ <a href="../../engine/core/Proofs.lean#L527">Engine.inv_front</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mem_purgeSet"></a>✅ <a href="../../engine/core/Proofs.lean#L366">Engine.mem_purgeSet</a> · 17 below</summary><ul>
<li>▫️ <a href="#law-Engine.closeUp_dependents">Engine.closeUp_dependents</a> ↪ · 12 below</li>
<li><details><summary><a id="law-Engine.closeUp_sound"></a>▫️ <a href="../../engine/core/Purge.lean#L312">Engine.closeUp_sound</a> · 11 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_walk">Engine.closeUp_walk</a> ↪ · 10 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.closeUp_sub">Engine.closeUp_sub</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/core/Purge.lean#L362">Engine.mem_purgeSet_iff</a></li>
<li>▫️ <a href="../../engine/core/Purge.lean#L319">Engine.reach_closed</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.reach_ops"></a>✅ <a href="../../engine/core/Proofs.lean#L641">Engine.reach_ops</a> · 12 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.reach_stored">Engine.reach_stored</a> ↪ · 10 below</li>
<li><details><summary><a id="law-Engine.reach_held"></a>▫️ <a href="../../engine/core/Proofs.lean#L613">Engine.reach_held</a> · 9 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.stepS_ops">Engine.stepS_ops</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.has_false">Engine.has_false</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sum_left"></a>✅ <a href="../../engine/core/Families.lean#L81">Engine.sum_left</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Families.lean#L75">Engine.lefts_map</a></li>
</ul></details></li>
<li><a id="law-Engine.sum_scope_left"></a>✅ <a href="../../engine/core/Families.lean#L86">Engine.sum_scope_left</a></li>
<li><a id="law-Engine.Codec.decode_encode"></a>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li><details><summary><a id="law-Engine.Op.decode_bytes"></a>✅ <a href="../../engine/core/Core.lean#L97">Engine.Op.decode_bytes</a> · 34 below</summary><ul>
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
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.trace_good"></a>🌐 <a href="../../app/Proofs.lean#L2865">Connection.Execution.trace_good</a> · 242 below</summary><ul>
<li>📐 <a href="security-proofs-connections.md#law-Connection.Execution.empty_trace_store">Connection.Execution.empty_trace_store</a> ↪ · 241 below</li>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.Run.good"></a>🌐 <a href="../../app/Proofs.lean#L2948">Connection.Execution.Run.good</a> · 244 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.trace_good">Connection.Execution.trace_good</a> ↪ · 242 below</li>
<li>🌐 <a href="../../app/Proofs.lean#L2936">Connection.Execution.Run.state_trace</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.admitted_trace"></a>🌐 <a href="../../app/Proofs.lean#L2917">Connection.Execution.admitted_trace</a> · 321 below</summary><ul>
<li>📐 <a href="security-proofs-connections.md#law-Connection.Execution.trace_rest">Connection.Execution.trace_rest</a> ↪ · 279 below</li>
<li><details><summary><a id="law-Connection.admitted_node"></a>✅ <a href="../../app/Proofs.lean#L1095">Connection.admitted_node</a> · 81 below</summary><ul>
<li>✅ <a href="#law-Connection.sum_project_node">Connection.sum_project_node</a> ↪ · 80 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/connection/Proofs.lean#L774">Connection.community_ops</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sum_project"></a>✅ <a href="../../engine/core/Project.lean#L427">Engine.sum_project</a> · 40 below</summary><ul>
<li>✅ <a href="#law-Engine.view_proj">Engine.view_proj</a> ↪ · 34 below</li>
<li><details><summary><a id="law-Engine.proj_inv"></a>✅ <a href="../../engine/core/Project.lean#L220">Engine.proj_inv</a> · 32 below</summary><ul>
<li><details><summary><a id="law-Engine.proj_status"></a>✅ <a href="../../engine/core/Project.lean#L210">Engine.proj_status</a> · 25 below</summary><ul>
<li>✅ <a href="#law-Engine.spec_sum_left">Engine.spec_sum_left</a> ↪ · 19 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li><details><summary><a id="law-Engine.specVerdict_eq_some"></a>📐 <a href="../../engine/core/Project.lean#L71">Engine.specVerdict_eq_some</a> · 8 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="#law-Engine.specVerdict_eq_some">Engine.specVerdict_eq_some</a> ↪ · 8 below</li>
<li>▫️ <a href="#law-Engine.spec_of_judge">Engine.spec_of_judge</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.leftOps_isSome"></a>📐 <a href="../../engine/core/Project.lean#L56">Engine.leftOps_isSome</a> · 1 below</summary><ul>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L215">Engine.mem_proj_idx</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L206">Engine.proj_ops</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.spec_sum_left">Engine.spec_sum_left</a> ↪ · 19 below</li>
<li>✅ <a href="#law-Engine.status_iff_spec">Engine.status_iff_spec</a> ↪ · 9 below</li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.sum_project_node"></a>✅ <a href="../../app/connection/Family.lean#L676">Connection.sum_project_node</a> · 80 below</summary><ul>
<li>✅ <a href="#law-Engine.sum_project">Engine.sum_project</a> ↪ · 40 below</li>
<li><details><summary><a id="law-Engine.leftKey_rels"></a>✅ <a href="../../engine/core/Project.lean#L337">Engine.leftKey_rels</a> · 35 below</summary><ul>
<li><details><summary><a id="law-Engine.leftKey_rel"></a>✅ <a href="../../engine/core/Project.lean#L322">Engine.leftKey_rel</a> · 34 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L298">Engine.leftKey_of</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="../../app/community/Family.lean#L1592">Community.rels_short</a></li>
<li>✅ <a href="../../app/connection/Family.lean#L665">Connection.rels_apart</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L289">Engine.View.Reads.mono</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.spec_sum_left"></a>✅ <a href="../../engine/core/Project.lean#L197">Engine.spec_sum_left</a> · 19 below</summary><ul>
<li><details><summary><a id="law-Engine.specAt_left"></a>✅ <a href="../../engine/core/Project.lean#L182">Engine.specAt_left</a> · 15 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>📐 <a href="security-proofs-connections.md#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L131">Engine.All2.to_map</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.specAt_inl"></a>✅ <a href="../../engine/core/Project.lean#L158">Engine.specAt_inl</a> · 14 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
<li>📐 <a href="security-proofs-connections.md#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/SpecLemmas.lean#L187">Engine.All2.imp</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L126">Engine.All2.of_map</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L41">Engine.leftOps_eq_some</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L138">Engine.lefts_some</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.view_proj"></a>✅ <a href="../../engine/core/Project.lean#L410">Engine.view_proj</a> · 34 below</summary><ul>
<li><details><summary><a id="law-Engine.eval_proj"></a>📐 <a href="../../engine/core/Project.lean#L387">Engine.eval_proj</a> · 32 below</summary><ul>
<li><details><summary><a id="law-Engine.matching_proj"></a>📐 <a href="../../engine/core/Project.lean#L366">Engine.matching_proj</a> · 31 below</summary><ul>
<li>✅ <a href="#law-Engine.proj_status">Engine.proj_status</a> ↪ · 25 below</li>
<li>✅ <a href="#law-Engine.sortPos_map">Engine.sortPos_map</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/View.lean#L128">Engine.filterMap_congr'</a></li>
<li>▫️ <a href="../../engine/core/Model.lean#L30">Engine.has_iff</a></li>
<li>📐 <a href="../../engine/core/Project.lean#L215">Engine.mem_proj_idx</a></li>
</ul></details></li>
</ul></details></li>
<li>📐 <a href="../../engine/core/Project.lean#L404">Engine.filterMap_inlRow</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.connect_iff_node"></a>✅ <a href="../../app/connection/Proofs.lean#L635">Connection.connect_iff_node</a> · 115 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_allowPeer">Community.reads_allowPeer</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.members_iff_node"></a>📐 <a href="../../app/connection/Proofs.lean#L479">Connection.members_iff_node</a> · 116 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>📐 <a href="security-proofs-confidentiality.md#law-Community.members_iff">Community.members_iff</a> ↪ · 69 below</li>
<li><details><summary><a id="law-Community.reads_members"></a>📐 <a href="../../app/connection/Family.lean#L648">Community.reads_members</a> · 5 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_live">Community.reads_live</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.recipients_iff_node"></a>📐 <a href="../../app/connection/Proofs.lean#L487">Connection.recipients_iff_node</a> · 116 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Connection.community_inv">Connection.community_inv</a> ↪ · 81 below</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.view_node">Connection.view_node</a> ↪ · 81 below</li>
<li>📐 <a href="security-proofs-confidentiality.md#law-Community.recipients_iff">Community.recipients_iff</a> ↪ · 69 below</li>
<li><details><summary><a id="law-Community.reads_recipients"></a>📐 <a href="../../app/connection/Family.lean#L652">Community.reads_recipients</a> · 5 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.reads_live">Community.reads_live</a> ↪ · 4 below</li>
<li>✅ <a href="../../engine/core/Project.lean#L280">Engine.View.Reads.bind</a></li>
<li>✅ <a href="../../engine/core/Project.lean#L286">Engine.View.Reads.read</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.node_settles"></a>✅ <a href="../../app/connection/Proofs.lean#L496">Connection.node_settles</a> · 67 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Engine.drain_terminates">Engine.drain_terminates</a> ↪ · 18 below</li>
<li>✅ <a href="../../engine/core/Proofs.lean#L543">Engine.reach_drain</a></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.current_newest"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L72">Settings.Appearance.current_newest</a> · 67 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.query_only"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L54">Settings.Appearance.query_only</a> · 40 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.query_right"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L45">Settings.Appearance.query_right</a> · 38 below</summary><ul>
<li><details><summary><a id="law-Settings.Appearance.not_relKey"></a>▫️ <a href="../../app/settings/appearance/Proofs.lean#L30">Settings.Appearance.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.key_ne_opKey"></a>▫️ <a href="../../app/settings/appearance/Proofs.lean#L41">Settings.Appearance.key_ne_opKey</a> · 30 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Left.lean#L129">Engine.rightKey_of</a></li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L25">Settings.Appearance.apart_community</a></li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L26">Settings.Appearance.apart_connection</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Settings.Appearance.not_relKey">Settings.Appearance.not_relKey</a> ↪ · 31 below</li>
<li>▫️ <a href="#law-Settings.Appearance.key_ne_opKey">Settings.Appearance.key_ne_opKey</a> ↪ · 30 below</li>
<li>▫️ <a href="../../app/settings/appearance/Proofs.lean#L27">Settings.Appearance.apart_nav</a></li>
</ul></details></li>
<li>✅ <a href="#law-Settings.Appearance.query_right">Settings.Appearance.query_right</a> ↪ · 38 below</li>
<li><details><summary><a id="law-Engine.top_right"></a>✅ <a href="../../engine/core/Left.lean#L142">Engine.top_right</a> · 25 below</summary><ul>
<li><details><summary><a id="law-Engine.top_max"></a>✅ <a href="../../engine/core/Order.lean#L173">Engine.top_max</a> · 21 below</summary><ul>
<li>✅ <a href="#law-Engine.sortPos_sorted">Engine.sortPos_sorted</a> ↪ · 15 below</li>
<li><details><summary><a id="law-Engine.sorted_last"></a>▫️ <a href="../../engine/core/Order.lean#L157">Engine.sorted_last</a> · 10 below</summary><ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Engine.Pos.cmp_eq_iff">Engine.Pos.cmp_eq_iff</a> ↪ · 9 below</li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.choose_valid"></a>✅ <a href="../../app/settings/appearance/Commands.lean#L18">Settings.Appearance.choose_valid</a> · 26 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../app/settings/appearance/Op.lean#L32">Settings.Appearance.ofCode_code</a></li>
</ul></details></li>
<li><details><summary><a id="law-Settings.Appearance.choose_local"></a>✅ <a href="../../app/settings/appearance/Proofs.lean#L19">Settings.Appearance.choose_local</a> · 24 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
</ul></details></li>
<li><details><summary><a id="law-Quiet.node_left"></a>✅ <a href="../../app/Family.lean#L105">Quiet.node_left</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.left_list"></a>✅ <a href="../../engine/core/Left.lean#L94">Engine.left_list</a> · 34 below</summary><ul>
<li>📐 <a href="#law-Engine.eval_proj">Engine.eval_proj</a> ↪ · 32 below</li>
<li>📐 <a href="../../engine/core/Project.lean#L404">Engine.filterMap_inlRow</a></li>
</ul></details></li>
<li><details><summary><a id="law-App.withNav_cache"></a>📐 <a href="../../app/nav/Proofs.lean#L128">App.withNav_cache</a> · 179 below</summary><ul>
<li>📐 <a href="#law-Data.placeIn_newest">Data.placeIn_newest</a> ↪ · 177 below</li>
<li>✅ <a href="../../app/Screen.lean#L2116">App.page_round</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.placeIn_newest"></a>📐 <a href="../../app/nav/Proofs.lean#L71">Data.placeIn_newest</a> · 177 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOps_valid"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L63">Engine.Sync.ofOps_valid</a> · 95 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ofOps_inv"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L50">Engine.Sync.ofOps_inv</a> · 68 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_inv">Engine.reach_inv</a> ↪ · 57 below</li>
<li><details><summary><a id="law-Engine.Sync.ofOps_reach"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L36">Engine.Sync.ofOps_reach</a> · 9 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Sync.turn_reachable">Engine.Sync.turn_reachable</a> ↪ · 7 below</li>
<li>✅ <a href="../../engine/sync/ClosureStore.lean#L171">Engine.Sync.held_empty_reachable</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.turn_nil_reqs"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L361">Engine.turn_nil_reqs</a> · 24 below</summary><ul>
<li><details><summary><a id="law-Engine.judgeJob_nil_reqs"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L350">Engine.judgeJob_nil_reqs</a> · 20 below</summary><ul>
<li><details><summary><a id="law-Engine.grows_judgeJob"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L323">Engine.grows_judgeJob</a> · 15 below</summary><ul>
<li>▫️ <a href="#law-Engine.grows_judgeAhead">Engine.grows_judgeAhead</a> ↪ · 13 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.judgeAheadS_ops">Engine.judgeAheadS_ops</a> ↪ · 8 below</li>
<li><details><summary><a id="law-Engine.judgeAhead_nil_reqs"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L333">Engine.judgeAhead_nil_reqs</a> · 5 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.decideS_fields">Engine.decideS_fields</a> ↪ · 4 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L70">Engine.Grows.isSome</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.grows_urgentClose"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L327">Engine.grows_urgentClose</a> · 15 below</summary><ul>
<li>▫️ <a href="#law-Engine.grows_judgeAhead">Engine.grows_judgeAhead</a> ↪ · 13 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.grows_drain">Engine.grows_drain</a> ↪ · 14 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L70">Engine.Grows.isSome</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ofOps_ops"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L55">Engine.Sync.ofOps_ops</a> · 23 below</summary><ul>
<li>✅ <a href="#law-Engine.reach_ops">Engine.reach_ops</a> ↪ · 12 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_reach">Engine.Sync.ofOps_reach</a> ↪ · 9 below</li>
</ul></details></li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Engine.turnCappedS_ops">Engine.turnCappedS_ops</a> ↪ · 12 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_det">Engine.spec_det</a> ↪ · 7 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ofOps_from"></a>✅ <a href="../../engine/sync/Ephemeral.lean#L81">Engine.Sync.ofOps_from</a> · 76 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 68 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_ops">Engine.Sync.ofOps_ops</a> ↪ · 23 below</li>
<li>📐 <a href="security-proofs-connections.md#law-Engine.specAt_valid_inv">Engine.specAt_valid_inv</a> ↪ · 1 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 68 below</li>
<li><details><summary><a id="law-Nav.query_only"></a>✅ <a href="../../app/nav/Proofs.lean#L39">Nav.query_only</a> · 39 below</summary><ul>
<li><details><summary><a id="law-Nav.not_relKey"></a>▫️ <a href="../../app/nav/Proofs.lean#L22">Nav.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Nav.key_ne_opKey"></a>▫️ <a href="../../app/nav/Proofs.lean#L33">Nav.key_ne_opKey</a> · 30 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
</ul></details></li>
<li>✅ <a href="../../engine/core/Left.lean#L129">Engine.rightKey_of</a></li>
<li>▫️ <a href="../../app/nav/Proofs.lean#L18">Nav.apart_community</a></li>
<li>▫️ <a href="../../app/nav/Proofs.lean#L19">Nav.apart_connection</a></li>
<li>▫️ <a href="../../app/nav/Proofs.lean#L20">Nav.apart_settings</a></li>
</ul></details></li>
<li><details><summary><a id="law-Nav.place_valid"></a>✅ <a href="../../app/nav/Commands.lean#L16">Nav.place_valid</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L127">Engine.Codec.decNat_encNat</a></li>
<li>✅ <a href="../../engine/core/Codec.lean#L767">Engine.Codec.decode_encode</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.top_right">Engine.top_right</a> ↪ · 25 below</li>
<li><details><summary><a id="law-Quiet.node_nav"></a>✅ <a href="../../app/Family.lean#L64">Quiet.node_nav</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/Family.lean#L48">Quiet.rights_map</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/sync/Ephemeral.lean#L29">Engine.Sync.run_eval</a></li>
<li>✅ <a href="../../app/Family.lean#L83">Quiet.node_nav_kind</a></li>
</ul></details></li>
<li><a id="law-Quiet.node_nav_ephemeral"></a>✅ <a href="../../app/Family.lean#L76">Quiet.node_nav_ephemeral</a></li>
<li><a id="law-Engine.intake_durable"></a>✅ <a href="../../engine/core/Sync.lean#L114">Engine.intake_durable</a></li>
<li><details><summary><a id="law-Engine.stored_durable"></a>✅ <a href="../../engine/core/Sync.lean#L204">Engine.stored_durable</a> · 13 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.stepS_ops-">Engine.stepS_ops'</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.foldl_ingest_ops">Engine.foldl_ingest_ops</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_mem">Engine.purgeS_ops_mem</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.purgeS_ops_not">Engine.purgeS_ops_not</a> ↪ · 1 below</li>
<li>✅ <a href="../../engine/core/Sync.lean#L114">Engine.intake_durable</a></li>
</ul></details></li>
<li><details><summary><a id="law-App.stash_use"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L257">App.stash_use</a> · 189 below</summary><ul>
<li>✅ <a href="#law-Data.draftIn_newest">Data.draftIn_newest</a> ↪ · 188 below</li>
</ul></details></li>
<li><details><summary><a id="law-Data.draftIn_newest"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L135">Data.draftIn_newest</a> · 188 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ofOps_valid">Engine.Sync.ofOps_valid</a> ↪ · 95 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_from">Engine.Sync.ofOps_from</a> ↪ · 76 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 68 below</li>
<li><details><summary><a id="law-Community.Draft.query_only"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L67">Community.Draft.query_only</a> · 42 below</summary><ul>
<li><details><summary><a id="law-Community.Draft.key_draft"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L28">Community.Draft.key_draft</a> · 33 below</summary><ul>
<li><details><summary><a id="law-Engine.Rel.key_eq_iff"></a>▫️ <a href="../../engine/core/Decl.lean#L65">Engine.Rel.key_eq_iff</a> · 30 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Codec.encode_inj">Engine.Codec.encode_inj</a> ↪ · 1 below</li>
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
<li><details><summary><a id="law-Community.Draft.rel_draft"></a>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L21">Community.Draft.rel_draft</a> · 1 below</summary><ul>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L19">Community.Draft.draft_rels</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.not_relKey"></a>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L51">Community.Draft.not_relKey</a> · 31 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_names">Engine.Rel.key_names</a> ↪ · 30 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.key_ne_opKey"></a>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L63">Community.Draft.key_ne_opKey</a> · 30 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Engine.Rel.key_ne_opKey">Engine.Rel.key_ne_opKey</a> ↪ · 29 below</li>
</ul></details></li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L47">Community.Draft.apart_connection</a></li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L49">Community.Draft.apart_nav</a></li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L48">Community.Draft.apart_settings</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.node_draft"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L89">Community.Draft.node_draft</a> · 41 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L81">Community.Draft.check_draft</a></li>
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
<li>✅ <a href="#law-Community.Draft.write_valid">Community.Draft.write_valid</a> ↪ · 41 below</li>
<li>✅ <a href="#law-Engine.top_max">Engine.top_max</a> ↪ · 21 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>✅ <a href="#law-Quiet.node_left">Quiet.node_left</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Community.Draft.isFor_of"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L121">Community.Draft.isFor_of</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.sum_left">Engine.sum_left</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L19">Community.Draft.draft_rels</a></li>
<li>✅ <a href="../../engine/sync/Ephemeral.lean#L29">Engine.Sync.run_eval</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.draftIn_empty"></a>✅ <a href="../../app/community/channel/message/draft/Proofs.lean#L219">Data.draftIn_empty</a> · 142 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.ofOps_from">Engine.Sync.ofOps_from</a> ↪ · 76 below</li>
<li>✅ <a href="#law-Engine.Sync.ofOps_inv">Engine.Sync.ofOps_inv</a> ↪ · 68 below</li>
<li>✅ <a href="#law-Community.Draft.query_only">Community.Draft.query_only</a> ↪ · 42 below</li>
<li>✅ <a href="#law-Community.Draft.node_draft">Community.Draft.node_draft</a> ↪ · 41 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>✅ <a href="#law-Community.Draft.isFor_of">Community.Draft.isFor_of</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/channel/message/draft/Proofs.lean#L202">Data.mem_eval_matching</a></li>
<li>✅ <a href="../../engine/sync/Ephemeral.lean#L29">Engine.Sync.run_eval</a></li>
</ul></details></li>
<li><details><summary><a id="law-Community.Draft.write_ephemeral"></a>✅ <a href="../../app/community/channel/message/draft/Commands.lean#L34">Community.Draft.write_ephemeral</a> · 42 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.body_mkOp">Community.body_mkOp</a> ↪ · 41 below</li>
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
<li><details><summary><a id="law-Community.Draft.write_valid"></a>✅ <a href="../../app/community/channel/message/draft/Commands.lean#L29">Community.Draft.write_valid</a> · 41 below</summary><ul>
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
<li><details><summary><a id="law-Engine.perm_sortPos"></a>✅ <a href="../../engine/core/Decl.lean#L133">Engine.perm_sortPos</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Decl.lean#L124">Engine.perm_insertBy</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sortPos_sorted"></a>✅ <a href="../../engine/core/Order.lean#L153">Engine.sortPos_sorted</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.insertBy_sorted"></a>▫️ <a href="../../engine/core/Order.lean#L132">Engine.insertBy_sorted</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_trans"></a>▫️ <a href="../../engine/core/Query.lean#L214">Engine.Pos.cmp_trans</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_lt_trans"></a>▫️ <a href="../../engine/core/Query.lean#L201">Engine.bcmp_lt_trans</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmp_eq"></a>▫️ <a href="../../engine/core/Query.lean#L193">Engine.bcmp_eq</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L153">Engine.lexCmp_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_swap"></a>▫️ <a href="../../engine/core/Query.lean#L190">Engine.bcmp_swap</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L140">Engine.lexCmp_swap</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_trans"></a>▫️ <a href="../../engine/core/Query.lean#L197">Engine.bcmp_trans</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq_lexCmp">Engine.bcmp_eq_lexCmp</a> ↪ · 3 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L169">Engine.lexCmp_trans</a></li>
</ul></details></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.bcmp_trans">Engine.bcmp_trans</a> ↪ · 5 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Pos.cmp_swap"></a>✅ <a href="../../engine/core/Query.lean#L211">Engine.Pos.cmp_swap</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_swap">Engine.bcmp_swap</a> ↪ · 5 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Decl.lean#L124">Engine.perm_insertBy</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sortPos_eq_fast"></a>✅ <a href="../../engine/core/Query.lean#L279">Engine.sortPos_eq_fast</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.posLE_trans"></a>▫️ <a href="../../engine/core/Query.lean#L253">Engine.posLE_trans</a> · 13 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.posLE_total"></a>▫️ <a href="../../engine/core/Query.lean#L256">Engine.posLE_total</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.insertBy_split"></a>▫️ <a href="../../engine/core/Query.lean#L260">Engine.insertBy_split</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.sortPos_map"></a>✅ <a href="../../engine/core/Project.lean#L359">Engine.sortPos_map</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/core/Project.lean#L350">Engine.insertBy_map</a></li>
</ul></details></li>
<li><a id="law-Engine.insertBy_map"></a>✅ <a href="../../engine/core/Project.lean#L350">Engine.insertBy_map</a></li>
<li><details><summary><a id="law-Engine.foldr_insertBy"></a>✅ <a href="../../engine/core/Union.lean#L113">Engine.foldr_insertBy</a> · 18 below</summary><ul>
<li>✅ <a href="#law-Engine.insertBy_merge">Engine.insertBy_merge</a> ↪ · 17 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.insertBy_merge"></a>✅ <a href="../../engine/core/Union.lean#L76">Engine.insertBy_merge</a> · 17 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_gt_of_le"></a>✅ <a href="../../engine/core/Query.lean#L242">Engine.Pos.cmp_gt_of_le</a> · 15 below</summary><ul>
<li><details><summary><a id="law-Engine.Pos.cmp_lt_le_trans"></a>✅ <a href="../../engine/core/Query.lean#L231">Engine.Pos.cmp_lt_le_trans</a> · 14 below</summary><ul>
<li>▫️ <a href="#law-Engine.Pos.cmp_trans">Engine.Pos.cmp_trans</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Pos.cmp_eq"></a>✅ <a href="../../engine/core/Query.lean#L227">Engine.Pos.cmp_eq</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.bcmp_eq">Engine.bcmp_eq</a> ↪ · 5 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Pos.cmp_swap">Engine.Pos.cmp_swap</a> ↪ · 6 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Query.lean#L250">Engine.posLE_iff</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.mergeRuns_eq_sortPos"></a>✅ <a href="../../engine/core/Union.lean#L121">Engine.mergeRuns_eq_sortPos</a> · 19 below</summary><ul>
<li>✅ <a href="#law-Engine.foldr_insertBy">Engine.foldr_insertBy</a> ↪ · 18 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.union_rows"></a>✅ <a href="../../engine/core/Union.lean#L167">Engine.union_rows</a> · 20 below</summary><ul>
<li>✅ <a href="#law-Engine.mergeRuns_eq_sortPos">Engine.mergeRuns_eq_sortPos</a> ↪ · 19 below</li>
</ul></details></li>
<li><details><summary><a id="law-Community.request_valid"></a>✅ <a href="../../app/community/member/invite/request/Proofs.lean#L49">Community.request_valid</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
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
<li><details><summary><a id="law-Community.approve_valid"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L65">Community.approve_valid</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
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
<li><details><summary><a id="law-Community.admit_admits"></a>✅ <a href="../../app/community/member/invite/request/approve/Proofs.lean#L83">Community.admit_admits</a> · 49 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.spec_valid_of">Engine.spec_valid_of</a> ↪ · 8 below</li>
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
<li><details><summary><a id="law-Community.connect_admitted"></a>✅ <a href="../../app/community/Proofs.lean#L847">Community.connect_admitted</a> · 85 below</summary><ul>
<li>✅ <a href="security-proofs-connections.md#law-Community.connect_iff">Community.connect_iff</a> ↪ · 68 below</li>
<li>✅ <a href="#law-Community.admit_admits">Community.admit_admits</a> ↪ · 49 below</li>
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
<li><details><summary><a id="law-Community.removeMember_valid"></a>✅ <a href="../../app/community/Proofs.lean#L455">Community.removeMember_valid</a> · 85 below</summary><ul>
<li><details><summary><a id="law-Community.row_filed"></a>▫️ <a href="../../app/community/Family.lean#L1629">Community.row_filed</a> · 55 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Community.filed">Community.filed</a> ↪ · 48 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.mem_matching">Engine.mem_matching</a> ↪ · 3 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L1563">Community.matching_also_nil</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1567">Community.mem_eval_matching</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.admin_removal_stands">Community.admin_removal_stands</a> ↪ · 49 below</li>
<li><details><summary><a id="law-Community.root_of_admission"></a>✅ <a href="../../app/community/Proofs.lean#L152">Community.root_of_admission</a> · 46 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.valid_inv">Community.valid_inv</a> ↪ · 43 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.check_admission">Community.check_admission</a> ↪ · 24 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decNatFrom_at">Engine.Codec.decNatFrom_at</a> ↪ · 15 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1319">Community.all2_cons2</a></li>
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
<li>✅ <a href="security-proofs-identity-and-membership.md#law-Community.valid_stays">Community.valid_stays</a> ↪ · 6 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Community.Body.decFrom_of">Community.Body.decFrom_of</a> ↪ · 3 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../app/community/Family.lean#L690">Community.Body.dec_of</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1624">Community.admission_byUser_args</a></li>
<li>▫️ <a href="../../app/community/Family.lean#L1642">Community.byDevice_args</a></li>
<li>▫️ <a href="../../app/community/member/admin/Proofs.lean#L34">Community.isAdmin_sound</a></li>
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
<li>▫️ <a href="../../engine/core/View.lean#L62">Engine.View.eval_bind</a></li>
</ul></details></li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Engine.ready_drain"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L247">Engine.ready_drain</a> · 21 below</summary><ul>
<li>▫️ <a href="#law-Engine.ready_step">Engine.ready_step</a> ↪ · 20 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ready_step"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L161">Engine.ready_step</a> · 20 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.stepS_pop">Engine.stepS_pop</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Grows.judge"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L60">Engine.Grows.judge</a> · 4 below</summary><ul>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.judge_mono">Engine.judge_mono</a> ↪ · 3 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L70">Engine.Grows.isSome</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L30">Engine.pos_append</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.grows_drain"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L239">Engine.grows_drain</a> · 14 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.grows_step">Engine.grows_step</a> ↪ · 12 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L57">Engine.Grows.trans</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ready_judgeAhead"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L197">Engine.ready_judgeAhead</a> · 21 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.stepS_pop">Engine.stepS_pop</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.ready_extend">Engine.ready_extend</a> ↪ · 7 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
<li>▫️ <a href="../../engine/core/TurnLaws.lean#L96">Engine.judgeAheadS_eq</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.ready_extend"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L76">Engine.ready_extend</a> · 7 below</summary><ul>
<li>▫️ <a href="#law-Engine.Grows.judge">Engine.Grows.judge</a> ↪ · 4 below</li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L70">Engine.Grows.isSome</a></li>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L30">Engine.pos_append</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.grows_ingest"></a>▫️ <a href="../../engine/core/CarryLaws.lean#L93">Engine.grows_ingest</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/CarryLaws.lean#L55">Engine.Grows.refl</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.write_store"></a>📐 <a href="../../engine/sync/ClosureStore.lean#L24">Engine.Sync.write_store</a> · 3 below</summary><ul>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Sync.HeldM.forIn_reads">Engine.Sync.HeldM.forIn_reads</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L25">Engine.Sync.HeldM.bind_apply</a></li>
<li>▫️ <a href="../../engine/wire/NodeLaws.lean#L28">Engine.Sync.HeldM.getOp_apply</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.bcmp_eq_lexCmp"></a>▫️ <a href="../../engine/core/Query.lean#L136">Engine.bcmp_eq_lexCmp</a> · 3 below</summary><ul>
<li><details><summary><a id="law-Engine.bcmpFrom_eq"></a>▫️ <a href="../../engine/core/Query.lean#L117">Engine.bcmpFrom_eq</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Query.lean#L113">Engine.drop_data_cons</a></li>
<li>▫️ <a href="../../engine/core/Query.lean#L110">Engine.drop_data_nil</a></li>
</ul></details></li>
</ul></details></li>
</ul>
