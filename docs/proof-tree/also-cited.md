# Also cited

<!-- written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit -->

[The proof tree](../PROOF-TREE.md): the laws the README cites outside its guarantee rows. Each opens to the laws its proof uses; a law drawn whole elsewhere links there (↪), and a subtree 5 levels down continues under [Deeper](#deeper).

✅ wired: about running code (1395) · 🌐 world: the node's code in a World (72) · 🪜 step: a step of a wired law (59) · 📐 model: over a model (73) · 🧪 control: a negative control (33) · ▫️ lemma: not audited (2258)

## What is proven

<ul>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.want_reaches">Engine.World.Plain.want_reaches</a> ↪ · 565 below</li>
</ul>

## Towards Proofs for n Clients

<ul>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.same_ops_same_verdicts">Engine.same_ops_same_verdicts</a> ↪ · 74 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.Sync.stream_delivers">Engine.Sync.stream_delivers</a> ↪ · 139 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.converge">Engine.World.Plain.converge</a> ↪ · 136 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.offline">Engine.World.Plain.offline</a> ↪ · 138 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.good_always">Engine.World.Plain.good_always</a> ↪ · 405 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.grows">Engine.World.Plain.grows</a> ↪ · 127 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.want_reaches">Engine.World.Plain.want_reaches</a> ↪ · 565 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Engine.World.Plain.drain">Engine.World.Plain.drain</a> ↪ · 199 below</li>
</ul>

## What is Assumed

<ul>
<li><a id="law-Community.unscoped_signs_all"></a>📐 <a href="../../app/community/Proofs.lean#L94">Community.unscoped_signs_all</a></li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.lbl_inj">Engine.Sync.lbl_inj</a> ↪ · 40 below</li>
<li><details><summary><a id="law-Merkle.no_injective_hash"></a>📐 <a href="../../engine/core/Merkle.lean#L272">Merkle.no_injective_hash</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/Merkle.lean#L260">Merkle.length_allBytes</a></li>
<li>▫️ <a href="../../engine/core/Merkle.lean#L264">Merkle.mem_allBytes</a></li>
</ul></details></li>
<li>✅ <a href="security-proofs-hostile-input.md#law-Merkle.assumptions_hold">Merkle.assumptions_hold</a> ↪ · 3 below</li>
<li>✅ <a href="security-proofs-confidentiality.md#law-Community.cryptoSeal_good">Community.cryptoSeal_good</a> ↪</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.Noise.suite_good">Connection.Noise.suite_good</a> ↪ · 3 below</li>
<li><a id="law-Community.ofSeed_signs"></a>✅ <a href="../../app/community/Commands.lean#L424">Community.ofSeed_signs</a></li>
<li><details><summary><a id="law-Trust.receive_as_model"></a>✅ <a href="../../engine/core/SqliteLaws.lean#L286">Trust.receive_as_model</a> · 57 below</summary><ul>
<li><details><summary><a id="law-Trust.turnCapped_sim"></a>✅ <a href="../../engine/core/SqliteLaws.lean#L276">Trust.turnCapped_sim</a> · 54 below</summary><ul>
<li><details><summary><a id="law-Trust.drain_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L189">Trust.drain_sim</a> · 48 below</summary><ul>
<li><details><summary><a id="law-Trust.step_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L169">Trust.step_sim</a> · 47 below</summary><ul>
<li><details><summary><a id="law-Trust.decide_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L154">Trust.decide_sim</a> · 43 below</summary><ul>
<li>▫️ <a href="#law-Trust.indexAll_sim">Trust.indexAll_sim</a> ↪ · 41 below</li>
<li>▫️ <a href="#law-Trust.pushAll_sim">Trust.pushAll_sim</a> ↪ · 41 below</li>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.waitOn_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L122">Trust.waitOn_sim</a> · 42 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L78">Trust.Sim.ite</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.statuses_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L114">Trust.statuses_sim</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L78">Trust.Sim.ite</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.judgeJob_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L259">Trust.judgeJob_sim</a> · 48 below</summary><ul>
<li><details><summary><a id="law-Trust.judgeAhead_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L241">Trust.judgeAhead_sim</a> · 47 below</summary><ul>
<li>▫️ <a href="#law-Trust.decide_sim">Trust.decide_sim</a> ↪ · 43 below</li>
<li>▫️ <a href="#law-Trust.waitOn_sim">Trust.waitOn_sim</a> ↪ · 42 below</li>
<li>▫️ <a href="#law-Trust.statuses_sim">Trust.statuses_sim</a> ↪ · 41 below</li>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L78">Trust.Sim.ite</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.urgentClose_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L267">Trust.urgentClose_sim</a> · 48 below</summary><ul>
<li>▫️ <a href="#law-Trust.judgeAhead_sim">Trust.judgeAhead_sim</a> ↪ · 47 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.ingest_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L146">Trust.ingest_sim</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Trust.Sim.forIn"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L92">Trust.Sim.forIn</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Trust.Sim.transact"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L231">Trust.Sim.transact</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L200">Trust.transact_ok</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.purge_as_model"></a>✅ <a href="../../engine/core/SqliteLaws.lean#L387">Trust.purge_as_model</a> · 62 below</summary><ul>
<li><details><summary><a id="law-Trust.purgeCapped_sim"></a>✅ <a href="../../engine/core/SqliteLaws.lean#L371">Trust.purgeCapped_sim</a> · 55 below</summary><ul>
<li>▫️ <a href="#law-Trust.drain_sim">Trust.drain_sim</a> ↪ · 48 below</li>
<li>▫️ <a href="#law-Trust.urgentClose_sim">Trust.urgentClose_sim</a> ↪ · 48 below</li>
<li><details><summary><a id="law-Trust.purge_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L352">Trust.purge_sim</a> · 46 below</summary><ul>
<li><details><summary><a id="law-Trust.unsettle_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L334">Trust.unsettle_sim</a> · 42 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L78">Trust.Sim.ite</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.deleteAll_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L345">Trust.deleteAll_sim</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Trust.pushAll_sim">Trust.pushAll_sim</a> ↪ · 41 below</li>
<li><details><summary><a id="law-Trust.walkDeps_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L324">Trust.walkDeps_sim</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Trust.Sim.throw"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L319">Trust.Sim.throw</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L49">Trust.sql_throw</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Trust.Sim.transact">Trust.Sim.transact</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L86">Trust.Sim.congr</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L364">Trust.scrub_sim</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.receive_refused"></a>✅ <a href="../../engine/core/SqliteLaws.lean#L310">Trust.receive_refused</a> · 35 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
</ul>

## Bootstrap witnesses and running-app checks

<ul>
<li><details><summary><a id="law-Engine.Sync.ServiceRun.eventually_emitted"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L167">Engine.Sync.ServiceRun.eventually_emitted</a> · 46 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.ext-">Engine.Op.ext'</a> ↪ · 30 below</li>
<li><details><summary><a id="law-Engine.Sync.ServiceRun.pending_until"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L150">Engine.Sync.ServiceRun.pending_until</a> · 14 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.ServiceRun.pending"></a>✅ <a href="../../engine/sync/ClosureDelivery.lean#L135">Engine.Sync.ServiceRun.pending</a> · 13 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.serveOwed_pending">Engine.Sync.serveOwed_pending</a> ↪ · 12 below</li>
<li>▫️ <a href="../../engine/sync/TimeLaws.lean#L9">Engine.Sync.instLawfulBEqByteArray_engine_1</a></li>
</ul></details></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.ServiceRun.pending">Engine.Sync.ServiceRun.pending</a> ↪ · 13 below</li>
</ul></details></li>
<li>🌐 <a href="quality-proofs-sync.md#law-Connection.Execution.fairRun_fair">Connection.Execution.fairRun_fair</a> ↪ · 6 below</li>
<li>🌐 <a href="quality-proofs-sync.md#law-Connection.Execution.successful_fair_extension">Connection.Execution.successful_fair_extension</a> ↪ · 9 below</li>
<li>📐 <a href="quality-proofs-sync.md#law-Engine.Sync.conn_runs_exchange">Engine.Sync.conn_runs_exchange</a> ↪ · 158 below</li>
<li>✅ <a href="quality-proofs-the-engine.md#law-Engine.Sync.closure_delivered">Engine.Sync.closure_delivered</a> ↪ · 184 below</li>
</ul>

## Where native code still decides

<ul>
<li>✅ <a href="quality-proofs-the-screen.md#law-Camera.src_in">Camera.src_in</a> ↪ · 1 below</li>
</ul>

## What else can we move into Lean?

<ul>
<li>✅ <a href="security-proofs-confidentiality.md#law-Community.cryptoSeal_good">Community.cryptoSeal_good</a> ↪</li>
<li>✅ <a href="security-proofs-connections.md#law-Connection.Noise.suite_good">Connection.Noise.suite_good</a> ↪ · 3 below</li>
<li>✅ <a href="quality-proofs-the-screen.md#law-Camera.src_in">Camera.src_in</a> ↪ · 1 below</li>
</ul>

## Layout

<ul>
<li><details><summary><a id="law-App.WriteAdmission.admitted_frames"></a>✅ <a href="../../engine/wire/WriteAdmission.lean#L33">App.WriteAdmission.admitted_frames</a> · 28 below</summary><ul>
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
<li><a id="law-App.WriteAdmission.admitted_count"></a>✅ <a href="../../engine/wire/WriteAdmission.lean#L45">App.WriteAdmission.admitted_count</a></li>
<li><a id="law-App.WriteAdmission.admitted_bytes"></a>✅ <a href="../../engine/wire/WriteAdmission.lean#L57">App.WriteAdmission.admitted_bytes</a></li>
<li><a id="law-Engine.Sync.write_first"></a>✅ <a href="../../engine/wire/LaneLaws.lean#L256">Engine.Sync.write_first</a></li>
<li><details><summary><a id="law-Engine.Sync.Outbox.native_batch_bounded"></a>✅ <a href="../../engine/wire/OutboxLaws.lean#L66">Engine.Sync.Outbox.native_batch_bounded</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Reserved.native_batch_bytes"></a>▫️ <a href="../../engine/wire/Reserved.lean#L228">Engine.Sync.Reserved.native_batch_bytes</a> · 8 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.Reserved.take_batch_bytes"></a>▫️ <a href="../../engine/wire/Reserved.lean#L190">Engine.Sync.Reserved.take_batch_bytes</a> · 5 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.take_bytes">Engine.Sync.take_bytes</a> ↪ · 4 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reserved.take_batch_count"></a>▫️ <a href="../../engine/wire/Reserved.lean#L205">Engine.Sync.Reserved.take_batch_count</a> · 2 below</summary><ul>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.cut_append">Engine.Sync.cut_append</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/Reserved.lean#L217">Engine.Sync.Reserved.framed_bytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Outbox.queued_bounded"></a>▫️ <a href="../../engine/wire/OutboxLaws.lean#L17">Engine.Sync.Outbox.queued_bounded</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/LaneLaws.lean#L116">Engine.Sync.bytesOf_append</a></li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Outbox.retry_next_batch"></a>✅ <a href="../../engine/wire/OutboxLaws.lean#L77">Engine.Sync.Outbox.retry_next_batch</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/OutboxLaws.lean#L73">Engine.Sync.Outbox.urgent_then_retry</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.Outbox.push_preserves_reserved"></a>✅ <a href="../../engine/wire/OutboxLaws.lean#L46">Engine.Sync.Outbox.push_preserves_reserved</a></li>
<li><details><summary><a id="law-Engine.Sync.Reserved.push_bounded"></a>✅ <a href="../../engine/wire/Reserved.lean#L145">Engine.Sync.Reserved.push_bounded</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/LaneLaws.lean#L130">Engine.Sync.push_capped</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Reserved.take_bounded"></a>✅ <a href="../../engine/wire/Reserved.lean#L166">Engine.Sync.Reserved.take_bounded</a> · 6 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.take_bytes">Engine.Sync.take_bytes</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.cut_append">Engine.Sync.cut_append</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/Reserved.lean#L161">Engine.Sync.Reserved.take_retry_bytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Outbox.push_bounded"></a>✅ <a href="../../engine/wire/OutboxLaws.lean#L27">Engine.Sync.Outbox.push_bounded</a> · 2 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.Reserved.push_bounded">Engine.Sync.Reserved.push_bounded</a> ↪ · 1 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Outbox.take_bounded"></a>✅ <a href="../../engine/wire/OutboxLaws.lean#L52">Engine.Sync.Outbox.take_bounded</a> · 6 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.take_bytes">Engine.Sync.take_bytes</a> ↪ · 4 below</li>
<li>▫️ <a href="quality-proofs-sync.md#law-Engine.Sync.cut_append">Engine.Sync.cut_append</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/Reserved.lean#L161">Engine.Sync.Reserved.take_retry_bytes</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.source_within"></a>✅ <a href="../../engine/wire/IngressLaws.lean#L158">Engine.Sync.Ingress.source_within</a> · 7 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.Ingress.served">Engine.Sync.Ingress.served</a> ↪ · 6 below</li>
<li>🪜 <a href="../../engine/wire/IngressLaws.lean#L5">Engine.Sync.Ingress.distance_lt</a> · a step of Engine.Sync.ExpiryGrace.source_before_exhaustion, Engine.Sync.Ingress.Prioritized.churnFlood_source, Engine.Sync.Ingress.Prioritized.poll_exists +8</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.Ingress.Prioritized.source_within"></a>✅ <a href="../../engine/wire/IngressPriorityLaws.lean#L133">Engine.Sync.Ingress.Prioritized.source_within</a> · 13 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.Ingress.Prioritized.served">Engine.Sync.Ingress.Prioritized.served</a> ↪ · 12 below</li>
<li>🪜 <a href="../../engine/wire/IngressLaws.lean#L5">Engine.Sync.Ingress.distance_lt</a> · a step of Engine.Sync.ExpiryGrace.source_before_exhaustion, Engine.Sync.Ingress.Prioritized.churnFlood_source, Engine.Sync.Ingress.Prioritized.poll_exists +8</li>
</ul></details></li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.Ingress.Prioritized.write_within">Engine.Sync.Ingress.Prioritized.write_within</a> ↪ · 6 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.Ingress.Prioritized.source_or_cancelled_within">Engine.Sync.Ingress.Prioritized.source_or_cancelled_within</a> ↪ · 16 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.Ingress.Prioritized.write_within_churn">Engine.Sync.Ingress.Prioritized.write_within_churn</a> ↪ · 7 below</li>
<li><a id="law-App.Presentation.bounded"></a>✅ <a href="../../engine/renderer/Presentation.lean#L43">App.Presentation.bounded</a></li>
<li><a id="law-App.Presentation.offer_append"></a>✅ <a href="../../engine/renderer/Presentation.lean#L46">App.Presentation.offer_append</a></li>
<li><a id="law-App.Presentation.offer_full"></a>✅ <a href="../../engine/renderer/Presentation.lean#L56">App.Presentation.offer_full</a></li>
<li><a id="law-App.Presentation.acknowledge_matches"></a>✅ <a href="../../engine/renderer/Presentation.lean#L67">App.Presentation.acknowledge_matches</a></li>
<li><a id="law-App.Presentation.transition_prior"></a>✅ <a href="../../engine/renderer/Presentation.lean#L94">App.Presentation.transition_prior</a></li>
<li><a id="law-App.Presentation.transition_rejected"></a>✅ <a href="../../engine/renderer/Presentation.lean#L100">App.Presentation.transition_rejected</a></li>
<li><a id="law-App.Presentation.transition_sound"></a>✅ <a href="../../engine/renderer/Presentation.lean#L106">App.Presentation.transition_sound</a></li>
<li><a id="law-Data.WriterQueue.push_local"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L10">Data.WriterQueue.push_local</a></li>
<li><a id="law-Data.WriterQueue.push_background"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L13">Data.WriterQueue.push_background</a></li>
<li><a id="law-Data.WriterQueue.push_keeps_phase"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L16">Data.WriterQueue.push_keeps_phase</a></li>
<li><details><summary><a id="law-Data.WriterQueue.local_fifo"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L20">Data.WriterQueue.local_fifo</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L10">Data.WriterQueue.push_local</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.WriterQueue.background_fifo"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L23">Data.WriterQueue.background_fifo</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L13">Data.WriterQueue.push_background</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.WriterQueue.local_first"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L27">Data.WriterQueue.local_first</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L33">Engine.Sync.Inbox.Priority.step_write</a></li>
</ul></details></li>
<li><details><summary><a id="law-Data.WriterQueue.background_slot"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L33">Data.WriterQueue.background_slot</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/PriorityLaws.lean#L39">Engine.Sync.Inbox.Priority.step_event</a></li>
</ul></details></li>
<li><a id="law-Data.WriterQueue.take_state"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L39">Data.WriterQueue.take_state</a></li>
<li>✅ <a href="quality-proofs-sync.md#law-Data.WriterQueue.local_within">Data.WriterQueue.local_within</a> ↪ · 9 below</li>
<li>✅ <a href="quality-proofs-sync.md#law-Data.WriterQueue.background_within">Data.WriterQueue.background_within</a> ↪ · 9 below</li>
<li><details><summary><a id="law-Data.WriterQueue.local_share"></a>✅ <a href="../../engine/renderer/WriteQueueLaws.lean#L64">Data.WriterQueue.local_share</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/PriorityLaws.lean#L28">Engine.Sync.Inbox.Priority.local_share</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.ExpiryGrace.same_generation"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L6">Engine.Sync.ExpiryGrace.same_generation</a></li>
<li><details><summary><a id="law-Engine.Sync.ExpiryGrace.no_rearm"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L10">Engine.Sync.ExpiryGrace.no_rearm</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L6">Engine.Sync.ExpiryGrace.same_generation</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ExpiryGrace.exhausted"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L14">Engine.Sync.ExpiryGrace.exhausted</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L6">Engine.Sync.ExpiryGrace.same_generation</a></li>
</ul></details></li>
<li><a id="law-Engine.Sync.ExpiryGrace.empty_no_delay"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L19">Engine.Sync.ExpiryGrace.empty_no_delay</a></li>
<li><a id="law-Engine.Sync.ExpiryGrace.fresh_clears"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L24">Engine.Sync.ExpiryGrace.fresh_clears</a></li>
<li><a id="law-Engine.Sync.ExpiryGrace.consume_keeps_generation"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L27">Engine.Sync.ExpiryGrace.consume_keeps_generation</a></li>
<li><a id="law-Engine.Sync.ExpiryGrace.consume_decreases"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L29">Engine.Sync.ExpiryGrace.consume_decreases</a></li>
<li><a id="law-Engine.Sync.ExpiryGrace.consume_saturates"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L33">Engine.Sync.ExpiryGrace.consume_saturates</a></li>
<li><a id="law-Engine.Sync.ExpiryGrace.consumed_left"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L39">Engine.Sync.ExpiryGrace.consumed_left</a></li>
<li><details><summary><a id="law-Engine.Sync.ExpiryGrace.budget_exhausted"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L44">Engine.Sync.ExpiryGrace.budget_exhausted</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L39">Engine.Sync.ExpiryGrace.consumed_left</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.ExpiryGrace.source_before_exhaustion"></a>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L52">Engine.Sync.ExpiryGrace.source_before_exhaustion</a> · 18 below</summary><ul>
<li>✅ <a href="quality-proofs-sync.md#law-Engine.Sync.Ingress.Prioritized.source_or_cancelled_within">Engine.Sync.Ingress.Prioritized.source_or_cancelled_within</a> ↪ · 16 below</li>
<li>✅ <a href="../../engine/wire/ExpiryGraceLaws.lean#L39">Engine.Sync.ExpiryGrace.consumed_left</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.offered_or_retired"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L259">Engine.Sync.RetryOrder.offered_or_retired</a> · 12 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.waiting_rank"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L222">Engine.Sync.RetryOrder.waiting_rank</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.scan_progress"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L114">Engine.Sync.RetryOrder.scan_progress</a> · 6 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.offered_members"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L53">Engine.Sync.RetryOrder.offered_members</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L49">Engine.Sync.RetryOrder.offered_perm</a></li>
</ul></details></li>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L7">Engine.Sync.RetryOrder.claim_false</a></li>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L13">Engine.Sync.RetryOrder.claim_ready</a></li>
<li>🪜 <a href="../../engine/wire/RetryOrderLaws.lean#L85">Engine.Sync.RetryOrder.filter_rank</a> · a step of Engine.Sync.RetryOrder.offered_or_retired, Engine.Sync.RetryOrder.offered_rank, Engine.Sync.RetryOrder.reconcile_rank +2</li>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L34">Engine.Sync.RetryOrder.scan_members</a></li>
</ul></details></li>
<li>✅ <a href="#law-Engine.Sync.RetryOrder.offered_members">Engine.Sync.RetryOrder.offered_members</a> ↪ · 1 below</li>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.offered_rank"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L101">Engine.Sync.RetryOrder.offered_rank</a> · 1 below</summary><ul>
<li>🪜 <a href="../../engine/wire/RetryOrderLaws.lean#L85">Engine.Sync.RetryOrder.filter_rank</a> · a step of Engine.Sync.RetryOrder.offered_or_retired, Engine.Sync.RetryOrder.offered_rank, Engine.Sync.RetryOrder.reconcile_rank +2</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.reconcile_rank"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L171">Engine.Sync.RetryOrder.reconcile_rank</a> · 1 below</summary><ul>
<li>🪜 <a href="../../engine/wire/RetryOrderLaws.lean#L85">Engine.Sync.RetryOrder.filter_rank</a> · a step of Engine.Sync.RetryOrder.offered_or_retired, Engine.Sync.RetryOrder.offered_rank, Engine.Sync.RetryOrder.reconcile_rank +2</li>
</ul></details></li>
<li>🪜 <a href="../../engine/wire/RetryOrderLaws.lean#L186">Engine.Sync.RetryOrder.eligible_spec</a> · a step of Engine.Sync.RetryOrder.offered_or_retired, Engine.Sync.RetryOrder.waiting_rank</li>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L67">Engine.Sync.RetryOrder.reconcile_members</a></li>
</ul></details></li>
</ul></details></li>
<li><a id="law-Engine.Sync.Ingress.Registry.freeze_input"></a>✅ <a href="../../engine/wire/IngressFreezeLaws.lean#L6">Engine.Sync.Ingress.Registry.freeze_input</a></li>
<li><a id="law-Engine.Sync.Ingress.Registry.freeze_preserves_state"></a>✅ <a href="../../engine/wire/IngressFreezeLaws.lean#L9">Engine.Sync.Ingress.Registry.freeze_preserves_state</a></li>
<li><a id="law-Engine.Sync.Ingress.Registry.freeze_preserves_owner"></a>✅ <a href="../../engine/wire/IngressFreezeLaws.lean#L12">Engine.Sync.Ingress.Registry.freeze_preserves_owner</a></li>
<li><a id="law-Engine.Sync.Ingress.Registry.frozen_refuses"></a>✅ <a href="../../engine/wire/IngressFreezeLaws.lean#L15">Engine.Sync.Ingress.Registry.frozen_refuses</a></li>
<li><a id="law-Engine.Sync.Ingress.Registry.freeze_preserves_poll"></a>✅ <a href="../../engine/wire/IngressFreezeLaws.lean#L19">Engine.Sync.Ingress.Registry.freeze_preserves_poll</a></li>
<li><a id="law-Engine.Sync.Ingress.Registry.freeze_idempotent"></a>✅ <a href="../../engine/wire/IngressFreezeLaws.lean#L22">Engine.Sync.Ingress.Registry.freeze_idempotent</a></li>
<li><a id="law-Engine.Sync.JobOwners.admitted_bounded"></a>✅ <a href="../../engine/wire/JobOwnersLaws.lean#L6">Engine.Sync.JobOwners.admitted_bounded</a></li>
<li><a id="law-Engine.Sync.JobOwners.full_refuses"></a>✅ <a href="../../engine/wire/JobOwnersLaws.lean#L13">Engine.Sync.JobOwners.full_refuses</a></li>
<li><a id="law-Engine.Sync.JobOwners.available_creates"></a>✅ <a href="../../engine/wire/JobOwnersLaws.lean#L19">Engine.Sync.JobOwners.available_creates</a></li>
<li><a id="law-Engine.Sync.NodeUnique.boot_valid"></a>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L87">Engine.Sync.NodeUnique.boot_valid</a></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.open_valid"></a>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L210">Engine.Sync.NodeUnique.open_valid</a> · 5 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.Ensures.bind_any"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L37">Engine.Sync.NodeUnique.Ensures.bind_any</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L22">Engine.Sync.NodeUnique.Ensures.any</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L90">Engine.Sync.NodeUnique.close_valid</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.sweepAll_valid"></a>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L337">Engine.Sync.NodeUnique.sweepAll_valid</a> · 10 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.sweep_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L325">Engine.Sync.NodeUnique.sweep_shape</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.Ensures.forIn-"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L47">Engine.Sync.NodeUnique.Ensures.forIn'</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.RetryOrder.offered_nodup"></a>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L59">Engine.Sync.RetryOrder.offered_nodup</a> · 1 below</summary><ul>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L49">Engine.Sync.RetryOrder.offered_perm</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
<li>✅ <a href="../../engine/wire/RetryOrderLaws.lean#L74">Engine.Sync.RetryOrder.reconcile_nodup</a></li>
<li>▫️ <a href="../../engine/core/WindowIndex.lean#L22">Engine.lawfulBEqByteArray</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.step_valid"></a>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L498">Engine.Sync.NodeUnique.step_valid</a> · 64 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onFrame_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L389">Engine.Sync.NodeUnique.onFrame_valid</a> · 52 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onSealed_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L361">Engine.Sync.NodeUnique.onSealed_valid</a> · 51 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.apply_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L288">Engine.Sync.NodeUnique.apply_valid</a> · 16 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.store_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L176">Engine.Sync.NodeUnique.store_valid</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.fanout_shape">Engine.Sync.NodeUnique.fanout_shape</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.put_shape">Engine.Sync.NodeUnique.put_shape</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.forIn-">Engine.Sync.NodeUnique.Ensures.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.recordGiven_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L137">Engine.Sync.NodeUnique.recordGiven_shape</a> · 6 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.put_shape">Engine.Sync.NodeUnique.put_shape</a> ↪ · 5 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.drop_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L95">Engine.Sync.NodeUnique.drop_valid</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L90">Engine.Sync.NodeUnique.close_valid</a></li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L104">Engine.Sync.NodeUnique.keys_map</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.finish_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L261">Engine.Sync.NodeUnique.finish_valid</a> · 11 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.follow_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L220">Engine.Sync.NodeUnique.follow_valid</a> · 8 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.NodeUnique.open_valid">Engine.Sync.NodeUnique.open_valid</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.forIn-">Engine.Sync.NodeUnique.Ensures.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.drop_valid">Engine.Sync.NodeUnique.drop_valid</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.flush_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L245">Engine.Sync.NodeUnique.flush_shape</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.fold_drop_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L98">Engine.Sync.NodeUnique.fold_drop_valid</a> · 2 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.drop_valid">Engine.Sync.NodeUnique.drop_valid</a> ↪ · 1 below</li>
</ul></details></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.serve_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L310">Engine.Sync.NodeUnique.serve_shape</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L104">Engine.Sync.NodeUnique.keys_map</a></li>
</ul></details></li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.forIn-">Engine.Sync.NodeUnique.Ensures.forIn'</a> ↪ · 2 below</li>
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
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.store_valid">Engine.Sync.NodeUnique.store_valid</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.finish_valid">Engine.Sync.NodeUnique.finish_valid</a> ↪ · 11 below</li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.write_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L119">Engine.Sync.NodeUnique.write_shape</a> · 4 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onTick_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L477">Engine.Sync.NodeUnique.onTick_valid</a> · 31 below</summary><ul>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onTickReserved_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L412">Engine.Sync.NodeUnique.onTickReserved_valid</a> · 29 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.apply_valid">Engine.Sync.NodeUnique.apply_valid</a> ↪ · 16 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.store_valid">Engine.Sync.NodeUnique.store_valid</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.finish_valid">Engine.Sync.NodeUnique.finish_valid</a> ↪ · 11 below</li>
<li>✅ <a href="#law-Engine.Sync.NodeUnique.sweepAll_valid">Engine.Sync.NodeUnique.sweepAll_valid</a> ↪ · 10 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.serve_shape">Engine.Sync.NodeUnique.serve_shape</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.forIn-">Engine.Sync.NodeUnique.Ensures.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onTickDirect_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L444">Engine.Sync.NodeUnique.onTickDirect_valid</a> · 24 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.apply_valid">Engine.Sync.NodeUnique.apply_valid</a> ↪ · 16 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.store_valid">Engine.Sync.NodeUnique.store_valid</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.finish_valid">Engine.Sync.NodeUnique.finish_valid</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.serve_shape">Engine.Sync.NodeUnique.serve_shape</a> ↪ · 5 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.sweep_shape">Engine.Sync.NodeUnique.sweep_shape</a> ↪ · 4 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.forIn-">Engine.Sync.NodeUnique.Ensures.forIn'</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onWrite_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L485">Engine.Sync.NodeUnique.onWrite_valid</a> · 20 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.store_valid">Engine.Sync.NodeUnique.store_valid</a> ↪ · 12 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.finish_valid">Engine.Sync.NodeUnique.finish_valid</a> ↪ · 11 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.onClose_valid"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L492">Engine.Sync.NodeUnique.onClose_valid</a> · 12 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.finish_valid">Engine.Sync.NodeUnique.finish_valid</a> ↪ · 11 below</li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.fold_drop_valid">Engine.Sync.NodeUnique.fold_drop_valid</a> ↪ · 2 below</li>
</ul></details></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.sql_step_valid"></a>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L509">Engine.Sync.NodeUnique.sql_step_valid</a> · 73 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.NodeUnique.step_valid">Engine.Sync.NodeUnique.step_valid</a> ↪ · 64 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
<li>▫️ <a href="../../engine/wire/IOLaws.lean#L10">Engine.Sync.io_lawful</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.production_step_unique"></a>📐 <a href="../../app/Proofs.lean#L3919">Connection.Execution.production_step_unique</a> · 66 below</summary><ul>
<li>✅ <a href="#law-Engine.Sync.NodeUnique.step_valid">Engine.Sync.NodeUnique.step_valid</a> ↪ · 64 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L76">Engine.Sync.NodeUnique.Ensures.state</a></li>
</ul></details></li>
<li>🌐 <a href="quality-proofs-sync.md#law-Connection.Execution.world_step_unique">Connection.Execution.world_step_unique</a> ↪ · 68 below</li>
<li><details><summary><a id="law-Connection.Execution.world_trace_unique"></a>🌐 <a href="../../app/Proofs.lean#L3979">Connection.Execution.world_trace_unique</a> · 69 below</summary><ul>
<li>🌐 <a href="quality-proofs-sync.md#law-Connection.Execution.world_step_unique">Connection.Execution.world_step_unique</a> ↪ · 68 below</li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.empty_trace_unique"></a>🌐 <a href="../../app/Proofs.lean#L3988">Connection.Execution.empty_trace_unique</a> · 71 below</summary><ul>
<li>🌐 <a href="#law-Connection.Execution.world_trace_unique">Connection.Execution.world_trace_unique</a> ↪ · 69 below</li>
<li>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L87">Engine.Sync.NodeUnique.boot_valid</a></li>
</ul></details></li>
<li><details><summary><a id="law-Connection.Execution.Run.unique"></a>🌐 <a href="../../app/Proofs.lean#L3996">Connection.Execution.Run.unique</a> · 70 below</summary><ul>
<li>🌐 <a href="quality-proofs-sync.md#law-Connection.Execution.world_step_unique">Connection.Execution.world_step_unique</a> ↪ · 68 below</li>
<li>✅ <a href="../../engine/wire/NodeUniqueLaws.lean#L87">Engine.Sync.NodeUnique.boot_valid</a></li>
</ul></details></li>
</ul>

## Full-app execution report

<ul>
<li>✅ <a href="#law-Engine.Sync.RetryOrder.offered_or_retired">Engine.Sync.RetryOrder.offered_or_retired</a> ↪ · 12 below</li>
<li>✅ <a href="quality-proofs-the-screen.md#law-FrameTimes.bounded">FrameTimes.bounded</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.Ingress.Registry.freeze_input">Engine.Sync.Ingress.Registry.freeze_input</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.Ingress.Registry.freeze_preserves_state">Engine.Sync.Ingress.Registry.freeze_preserves_state</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.Ingress.Registry.freeze_preserves_owner">Engine.Sync.Ingress.Registry.freeze_preserves_owner</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.Ingress.Registry.frozen_refuses">Engine.Sync.Ingress.Registry.frozen_refuses</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.Ingress.Registry.freeze_preserves_poll">Engine.Sync.Ingress.Registry.freeze_preserves_poll</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.Ingress.Registry.freeze_idempotent">Engine.Sync.Ingress.Registry.freeze_idempotent</a> ↪</li>
<li>✅ <a href="#law-App.WriteAdmission.admitted_frames">App.WriteAdmission.admitted_frames</a> ↪ · 28 below</li>
<li>✅ <a href="#law-App.WriteAdmission.admitted_count">App.WriteAdmission.admitted_count</a> ↪</li>
<li>✅ <a href="#law-App.WriteAdmission.admitted_bytes">App.WriteAdmission.admitted_bytes</a> ↪</li>
<li>✅ <a href="#law-Engine.Sync.write_first">Engine.Sync.write_first</a> ↪</li>
</ul>

## Deeper

Subtrees met 5 levels down, drawn whole here once.

<ul>
<li><details><summary><a id="law-Trust.indexAll_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L139">Trust.indexAll_sim</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.pushAll_sim"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L132">Trust.pushAll_sim</a> · 41 below</summary><ul>
<li>▫️ <a href="#law-Trust.Sim.op">Trust.Sim.op</a> ↪ · 35 below</li>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.encNatInto_eq">Engine.Codec.encNatInto_eq</a> ↪ · 8 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decLenFrom_at">Engine.Codec.decLenFrom_at</a> ↪ · 7 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decListFrom_at">Engine.Codec.decListFrom_at</a> ↪ · 4 below</li>
<li>▫️ <a href="security-proofs-confidentiality.md#law-Engine.Codec.decFromAs_tag">Engine.Codec.decFromAs_tag</a> ↪ · 3 below</li>
<li>▫️ <a href="#law-Trust.Sim.bind">Trust.Sim.bind</a> ↪ · 2 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.At.tag">Engine.Codec.At.tag</a> ↪ · 1 below</li>
<li>▫️ <a href="security-proofs-identity-and-membership.md#law-Engine.Codec.decBytesL_encBytesL">Engine.Codec.decBytesL_encBytesL</a> ↪ · 1 below</li>
<li>▫️ <a href="#law-Trust.Sim.pure">Trust.Sim.pure</a> ↪ · 1 below</li>
<li>▫️ <a href="../../engine/core/Codec.lean#L98">Engine.Codec.At.extract</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L67">Engine.Codec.At.left</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L94">Engine.Codec.At.length_le</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L70">Engine.Codec.At.right</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L519">Engine.Codec.decBytesFrom_unfold</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L711">Engine.Codec.decFromAs_at</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L590">Engine.Codec.decListF_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.Sim.op"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L107">Trust.Sim.op</a> · 35 below</summary><ul>
<li>▫️ <a href="security-proofs-connections.md#law-Engine.Op.make_eta">Engine.Op.make_eta</a> ↪ · 31 below</li>
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
<li>▫️ <a href="../../engine/core/Codec.lean#L722">Engine.Codec.encInto_tag</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L613">Engine.Codec.encListInto_eq</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L149">Engine.Codec.length_encNat_pos</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L604">Engine.Codec.length_le_encList</a></li>
<li>▫️ <a href="../../engine/core/Codec.lean#L111">Engine.Codec.push_toList</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.Sim.bind"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L66">Trust.Sim.bind</a> · 2 below</summary><ul>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L36">Trust.model_bind</a></li>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L30">Trust.sql_bind</a></li>
</ul></details></li>
<li><details><summary><a id="law-Trust.Sim.pure"></a>▫️ <a href="../../engine/core/SqliteLaws.lean#L60">Trust.Sim.pure</a> · 1 below</summary><ul>
<li>▫️ <a href="../../engine/core/SqliteLaws.lean#L33">Trust.sql_pure</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.fanout_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L150">Engine.Sync.NodeUnique.fanout_shape</a> · 10 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.recordGiven_shape">Engine.Sync.NodeUnique.recordGiven_shape</a> ↪ · 6 below</li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.Ensures.forIn_fold"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L63">Engine.Sync.NodeUnique.Ensures.forIn_fold</a> · 3 below</summary><ul>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L41">Engine.Sync.NodeUnique.Ensures.mono</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
</ul></details></li>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.Ensures.bind_any">Engine.Sync.NodeUnique.Ensures.bind_any</a> ↪ · 2 below</li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L25">Engine.Sync.NodeUnique.Ensures.bind'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L19">Engine.Sync.NodeUnique.Ensures.pure'</a></li>
<li>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L144">Engine.Sync.NodeUnique.fold_keys</a></li>
</ul></details></li>
<li><details><summary><a id="law-Engine.Sync.NodeUnique.put_shape"></a>▫️ <a href="../../engine/wire/NodeUniqueLaws.lean#L133">Engine.Sync.NodeUnique.put_shape</a> · 5 below</summary><ul>
<li>▫️ <a href="#law-Engine.Sync.NodeUnique.write_shape">Engine.Sync.NodeUnique.write_shape</a> ↪ · 4 below</li>
</ul></details></li>
</ul>
