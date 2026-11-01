# Headline laws: the surfaces in full

Written by ci/headline.py from tests/Headline.lean's output; do not
edit. For each recommended law of [HEADLINE.md](HEADLINE.md), the
definitions of its spec surface that are the app's own code: what the
law is about, which runs in the app (its spec-only and assumed parts,
which a reviewer must read, are in HEADLINE.md). Then, for each law also
considered and each law not yet about running code, what its statement
names and its spec-only, assumed and bridged parts.

## Community.no_impersonation

<details><summary>Of the app: 298 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.byRequest`, `Community.Abandon.check`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.check`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Fact`, `Community.Admit.check`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.byRequest`, `Community.Approve.check`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.byMessage`, `Community.Attach.check`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.community`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.isLocal`, `Community.Body.post`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.byAttachment`, `Community.Chunk.check`, `Community.Chunk.instCodecBody`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.byId`, `Community.ContentKey.check`, `Community.ContentKey.instCodecBody`, `Community.Crypto`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.check`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admin?`, `Community.Fact.admission?`, `Community.Fact.approval?`, `Community.Fact.attachment?`, `Community.Fact.chunk?`, `Community.Fact.endpoint?`, `Community.Fact.isLocal`, `Community.Fact.joining?`, `Community.Fact.key?`, `Community.Fact.message?`, `Community.Fact.named?`, `Community.Fact.profile?`, `Community.Fact.react?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.request?`, `Community.Fact.secret?`, `Community.Fact.wrap?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.byUser`, `Community.Grant.check`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.check`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.check`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.all`, `Community.Post.byAuthor`, `Community.Post.byKey`, `Community.Post.check`, `Community.Post.childrenByKey`, `Community.Post.instCodecBody`, `Community.Post.rootsByKey`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.all`, `Community.Profile.byLook`, `Community.Profile.byUser`, `Community.Profile.check`, `Community.Profile.instCodecBody`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.byMessage`, `Community.React.byMessageEmoji`, `Community.React.check`, `Community.React.instCodecBody`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byKey`, `Community.Receive.byMsg`, `Community.Receive.check`, `Community.Receive.childrenByKey`, `Community.Receive.instCodecBody`, `Community.Receive.rootsByKey`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.check`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.check`, `Community.Rename.current`, `Community.Rename.instCodecBody`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.all`, `Community.Request.check`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.all`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.byUser`, `Community.Root.check`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.all`, `Community.Secret.byKey`, `Community.Secret.check`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.byContentKey`, `Community.Wrap.byRecipient`, `Community.Wrap.check`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.abandoned.byRequest`, `Community.accepted.all`, `Community.admin.byUser`, `Community.admission.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.admission.byUser`, `Community.approval.byRequest`, `Community.attachment.byMessage`, `Community.check`, `Community.chunk.byAttachment`, `Community.countCap`, `Community.counterOk`, `Community.cryptoSeal`, `Community.decWith`, `Community.endpoint.all`, `Community.family`, `Community.instCodecBody`, `Community.isAdmin`, `Community.isBlank`, `Community.joining.all`, `Community.key.byCommunity`, `Community.key.byId`, `Community.keys`, `Community.kidOf`, `Community.look`, `Community.maxFile`, `Community.maxSealedMeta`, `Community.message.all`, `Community.message.byAuthor`, `Community.message.byKey`, `Community.message.childrenByKey`, `Community.message.rootsByKey`, `Community.nameLook`, `Community.named.current`, `Community.orderOf`, `Community.prevMax`, `Community.profile.all`, `Community.profile.byLook`, `Community.profile.byUser`, `Community.react.byMessage`, `Community.react.byMessageEmoji`, `Community.received.all`, `Community.received.byKey`, `Community.received.byMsg`, `Community.received.childrenByKey`, `Community.received.rootsByKey`, `Community.rels`, `Community.removal.byUser`, `Community.request.all`, `Community.scopeOf`, `Community.secret.all`, `Community.secret.byKey`, `Community.signedBy`, `Community.validate`, `Community.wrap.byContentKey`, `Community.wrap.byRecipient`, `Engine.Bytes`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Family`, `Engine.Id`, `Engine.Key32`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Scope`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.allValid`, `Engine.anyInvalid`, `Engine.instTickId`, `Engine.judge`, `Engine.keysOf`, `Engine.sha256`, `Merkle.B`, `Merkle.be64`, `Merkle.climb`, `Merkle.depthOf`, `Merkle.leaf`, `Merkle.nChunks`, `Merkle.node`, `Merkle.rootOf`, `Merkle.sliceLen`, `Merkle.sliceSize`, `Merkle.tagLeaf`, `Merkle.tagNode`, `Merkle.tagRoot`, `Merkle.verify`, `Text.inRange`, `Text.isInvisible`

</details>

## Community.admission_needs_approval

<details><summary>Of the app: 297 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.byRequest`, `Community.Abandon.check`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.check`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Fact`, `Community.Admit.check`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.byRequest`, `Community.Approve.check`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.byMessage`, `Community.Attach.check`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.community`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.isLocal`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.byAttachment`, `Community.Chunk.check`, `Community.Chunk.instCodecBody`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.byId`, `Community.ContentKey.check`, `Community.ContentKey.instCodecBody`, `Community.Crypto`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.check`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admin?`, `Community.Fact.admission?`, `Community.Fact.approval?`, `Community.Fact.attachment?`, `Community.Fact.chunk?`, `Community.Fact.endpoint?`, `Community.Fact.isLocal`, `Community.Fact.joining?`, `Community.Fact.key?`, `Community.Fact.message?`, `Community.Fact.named?`, `Community.Fact.profile?`, `Community.Fact.react?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.request?`, `Community.Fact.secret?`, `Community.Fact.wrap?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.byUser`, `Community.Grant.check`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.check`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.check`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.all`, `Community.Post.byAuthor`, `Community.Post.byKey`, `Community.Post.check`, `Community.Post.childrenByKey`, `Community.Post.instCodecBody`, `Community.Post.rootsByKey`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.all`, `Community.Profile.byLook`, `Community.Profile.byUser`, `Community.Profile.check`, `Community.Profile.instCodecBody`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.byMessage`, `Community.React.byMessageEmoji`, `Community.React.check`, `Community.React.instCodecBody`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byKey`, `Community.Receive.byMsg`, `Community.Receive.check`, `Community.Receive.childrenByKey`, `Community.Receive.instCodecBody`, `Community.Receive.rootsByKey`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.check`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.check`, `Community.Rename.current`, `Community.Rename.instCodecBody`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.all`, `Community.Request.check`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.all`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.byUser`, `Community.Root.check`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.all`, `Community.Secret.byKey`, `Community.Secret.check`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.byContentKey`, `Community.Wrap.byRecipient`, `Community.Wrap.check`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.abandoned.byRequest`, `Community.accepted.all`, `Community.admin.byUser`, `Community.admission.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.admission.byUser`, `Community.approval.byRequest`, `Community.attachment.byMessage`, `Community.check`, `Community.chunk.byAttachment`, `Community.countCap`, `Community.counterOk`, `Community.cryptoSeal`, `Community.decWith`, `Community.endpoint.all`, `Community.family`, `Community.instCodecBody`, `Community.isAdmin`, `Community.isBlank`, `Community.joining.all`, `Community.key.byCommunity`, `Community.key.byId`, `Community.keys`, `Community.kidOf`, `Community.look`, `Community.maxFile`, `Community.maxSealedMeta`, `Community.message.all`, `Community.message.byAuthor`, `Community.message.byKey`, `Community.message.childrenByKey`, `Community.message.rootsByKey`, `Community.nameLook`, `Community.named.current`, `Community.orderOf`, `Community.prevMax`, `Community.profile.all`, `Community.profile.byLook`, `Community.profile.byUser`, `Community.react.byMessage`, `Community.react.byMessageEmoji`, `Community.received.all`, `Community.received.byKey`, `Community.received.byMsg`, `Community.received.childrenByKey`, `Community.received.rootsByKey`, `Community.rels`, `Community.removal.byUser`, `Community.request.all`, `Community.scopeOf`, `Community.secret.all`, `Community.secret.byKey`, `Community.signedBy`, `Community.validate`, `Community.wrap.byContentKey`, `Community.wrap.byRecipient`, `Engine.Bytes`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Family`, `Engine.Id`, `Engine.Key32`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Scope`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.allValid`, `Engine.anyInvalid`, `Engine.instTickId`, `Engine.judge`, `Engine.keysOf`, `Engine.sha256`, `Merkle.B`, `Merkle.be64`, `Merkle.climb`, `Merkle.depthOf`, `Merkle.leaf`, `Merkle.nChunks`, `Merkle.node`, `Merkle.rootOf`, `Merkle.sliceLen`, `Merkle.sliceSize`, `Merkle.tagLeaf`, `Merkle.tagNode`, `Merkle.tagRoot`, `Merkle.verify`, `Text.inRange`, `Text.isInvisible`

</details>

## Community.removal_authorized

<details><summary>Of the app: 297 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.byRequest`, `Community.Abandon.check`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.check`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Fact`, `Community.Admit.check`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.byRequest`, `Community.Approve.check`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.byMessage`, `Community.Attach.check`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.community`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.isLocal`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.byAttachment`, `Community.Chunk.check`, `Community.Chunk.instCodecBody`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.byId`, `Community.ContentKey.check`, `Community.ContentKey.instCodecBody`, `Community.Crypto`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.check`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admin?`, `Community.Fact.admission?`, `Community.Fact.approval?`, `Community.Fact.attachment?`, `Community.Fact.chunk?`, `Community.Fact.endpoint?`, `Community.Fact.isLocal`, `Community.Fact.joining?`, `Community.Fact.key?`, `Community.Fact.message?`, `Community.Fact.named?`, `Community.Fact.profile?`, `Community.Fact.react?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.request?`, `Community.Fact.secret?`, `Community.Fact.wrap?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.byUser`, `Community.Grant.check`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.check`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.check`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.all`, `Community.Post.byAuthor`, `Community.Post.byKey`, `Community.Post.check`, `Community.Post.childrenByKey`, `Community.Post.instCodecBody`, `Community.Post.rootsByKey`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.all`, `Community.Profile.byLook`, `Community.Profile.byUser`, `Community.Profile.check`, `Community.Profile.instCodecBody`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.byMessage`, `Community.React.byMessageEmoji`, `Community.React.check`, `Community.React.instCodecBody`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byKey`, `Community.Receive.byMsg`, `Community.Receive.check`, `Community.Receive.childrenByKey`, `Community.Receive.instCodecBody`, `Community.Receive.rootsByKey`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.check`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.check`, `Community.Rename.current`, `Community.Rename.instCodecBody`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.all`, `Community.Request.check`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.all`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.byUser`, `Community.Root.check`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.all`, `Community.Secret.byKey`, `Community.Secret.check`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.byContentKey`, `Community.Wrap.byRecipient`, `Community.Wrap.check`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.abandoned.byRequest`, `Community.accepted.all`, `Community.admin.byUser`, `Community.admission.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.admission.byUser`, `Community.approval.byRequest`, `Community.attachment.byMessage`, `Community.check`, `Community.chunk.byAttachment`, `Community.countCap`, `Community.counterOk`, `Community.cryptoSeal`, `Community.decWith`, `Community.endpoint.all`, `Community.family`, `Community.instCodecBody`, `Community.isAdmin`, `Community.isBlank`, `Community.joining.all`, `Community.key.byCommunity`, `Community.key.byId`, `Community.keys`, `Community.kidOf`, `Community.look`, `Community.maxFile`, `Community.maxSealedMeta`, `Community.message.all`, `Community.message.byAuthor`, `Community.message.byKey`, `Community.message.childrenByKey`, `Community.message.rootsByKey`, `Community.nameLook`, `Community.named.current`, `Community.orderOf`, `Community.prevMax`, `Community.profile.all`, `Community.profile.byLook`, `Community.profile.byUser`, `Community.react.byMessage`, `Community.react.byMessageEmoji`, `Community.received.all`, `Community.received.byKey`, `Community.received.byMsg`, `Community.received.childrenByKey`, `Community.received.rootsByKey`, `Community.rels`, `Community.removal.byUser`, `Community.request.all`, `Community.scopeOf`, `Community.secret.all`, `Community.secret.byKey`, `Community.signedBy`, `Community.validate`, `Community.wrap.byContentKey`, `Community.wrap.byRecipient`, `Engine.Bytes`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Family`, `Engine.Id`, `Engine.Key32`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Scope`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.allValid`, `Engine.anyInvalid`, `Engine.instTickId`, `Engine.judge`, `Engine.keysOf`, `Engine.sha256`, `Merkle.B`, `Merkle.be64`, `Merkle.climb`, `Merkle.depthOf`, `Merkle.leaf`, `Merkle.nChunks`, `Merkle.node`, `Merkle.rootOf`, `Merkle.sliceLen`, `Merkle.sliceSize`, `Merkle.tagLeaf`, `Merkle.tagNode`, `Merkle.tagRoot`, `Merkle.verify`, `Text.inRange`, `Text.isInvisible`

</details>

## Community.removed_stays

<details><summary>Of the app: 297 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.byRequest`, `Community.Abandon.check`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.check`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Fact`, `Community.Admit.check`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.byRequest`, `Community.Approve.check`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.byMessage`, `Community.Attach.check`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.community`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.isLocal`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.byAttachment`, `Community.Chunk.check`, `Community.Chunk.instCodecBody`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.byId`, `Community.ContentKey.check`, `Community.ContentKey.instCodecBody`, `Community.Crypto`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.check`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admin?`, `Community.Fact.admission?`, `Community.Fact.approval?`, `Community.Fact.attachment?`, `Community.Fact.chunk?`, `Community.Fact.endpoint?`, `Community.Fact.isLocal`, `Community.Fact.joining?`, `Community.Fact.key?`, `Community.Fact.message?`, `Community.Fact.named?`, `Community.Fact.profile?`, `Community.Fact.react?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.request?`, `Community.Fact.secret?`, `Community.Fact.wrap?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.byUser`, `Community.Grant.check`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.check`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.check`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.all`, `Community.Post.byAuthor`, `Community.Post.byKey`, `Community.Post.check`, `Community.Post.childrenByKey`, `Community.Post.instCodecBody`, `Community.Post.rootsByKey`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.all`, `Community.Profile.byLook`, `Community.Profile.byUser`, `Community.Profile.check`, `Community.Profile.instCodecBody`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.byMessage`, `Community.React.byMessageEmoji`, `Community.React.check`, `Community.React.instCodecBody`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byKey`, `Community.Receive.byMsg`, `Community.Receive.check`, `Community.Receive.childrenByKey`, `Community.Receive.instCodecBody`, `Community.Receive.rootsByKey`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.check`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.check`, `Community.Rename.current`, `Community.Rename.instCodecBody`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.all`, `Community.Request.check`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.all`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.byUser`, `Community.Root.check`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.all`, `Community.Secret.byKey`, `Community.Secret.check`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.byContentKey`, `Community.Wrap.byRecipient`, `Community.Wrap.check`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.abandoned.byRequest`, `Community.accepted.all`, `Community.admin.byUser`, `Community.admission.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.admission.byUser`, `Community.approval.byRequest`, `Community.attachment.byMessage`, `Community.check`, `Community.chunk.byAttachment`, `Community.countCap`, `Community.counterOk`, `Community.cryptoSeal`, `Community.decWith`, `Community.endpoint.all`, `Community.family`, `Community.instCodecBody`, `Community.isAdmin`, `Community.isBlank`, `Community.joining.all`, `Community.key.byCommunity`, `Community.key.byId`, `Community.keys`, `Community.kidOf`, `Community.look`, `Community.maxFile`, `Community.maxSealedMeta`, `Community.message.all`, `Community.message.byAuthor`, `Community.message.byKey`, `Community.message.childrenByKey`, `Community.message.rootsByKey`, `Community.nameLook`, `Community.named.current`, `Community.orderOf`, `Community.prevMax`, `Community.profile.all`, `Community.profile.byLook`, `Community.profile.byUser`, `Community.react.byMessage`, `Community.react.byMessageEmoji`, `Community.received.all`, `Community.received.byKey`, `Community.received.byMsg`, `Community.received.childrenByKey`, `Community.received.rootsByKey`, `Community.rels`, `Community.removal.byUser`, `Community.request.all`, `Community.scopeOf`, `Community.secret.all`, `Community.secret.byKey`, `Community.signedBy`, `Community.validate`, `Community.wrap.byContentKey`, `Community.wrap.byRecipient`, `Engine.Bytes`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Family`, `Engine.Id`, `Engine.Key32`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Scope`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.allValid`, `Engine.anyInvalid`, `Engine.instTickId`, `Engine.judge`, `Engine.keysOf`, `Engine.sha256`, `Merkle.B`, `Merkle.be64`, `Merkle.climb`, `Merkle.depthOf`, `Merkle.leaf`, `Merkle.nChunks`, `Merkle.node`, `Merkle.rootOf`, `Merkle.sliceLen`, `Merkle.sliceSize`, `Merkle.tagLeaf`, `Merkle.tagNode`, `Merkle.tagRoot`, `Merkle.verify`, `Text.inRange`, `Text.isInvisible`

</details>

## Community.connect_iff

<details><summary>Of the app: 326 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.byRequest`, `Community.Abandon.check`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.check`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Fact`, `Community.Admit.check`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.byRequest`, `Community.Approve.check`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.byMessage`, `Community.Attach.check`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.community`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.isLocal`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.byAttachment`, `Community.Chunk.check`, `Community.Chunk.instCodecBody`, `Community.Chunk.sortKey`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.byId`, `Community.ContentKey.check`, `Community.ContentKey.instCodecBody`, `Community.Crypto`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.check`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admin?`, `Community.Fact.admission?`, `Community.Fact.approval?`, `Community.Fact.attachment?`, `Community.Fact.chunk?`, `Community.Fact.endpoint?`, `Community.Fact.isLocal`, `Community.Fact.joining?`, `Community.Fact.key?`, `Community.Fact.message?`, `Community.Fact.named?`, `Community.Fact.profile?`, `Community.Fact.react?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.request?`, `Community.Fact.secret?`, `Community.Fact.wrap?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.byUser`, `Community.Grant.check`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.check`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.check`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.all`, `Community.Post.byAuthor`, `Community.Post.byKey`, `Community.Post.check`, `Community.Post.childrenByKey`, `Community.Post.instCodecBody`, `Community.Post.rootsByKey`, `Community.Post.sortKey`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.all`, `Community.Profile.byLook`, `Community.Profile.byUser`, `Community.Profile.check`, `Community.Profile.instCodecBody`, `Community.Profile.sortKey`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.byMessage`, `Community.React.byMessageEmoji`, `Community.React.check`, `Community.React.instCodecBody`, `Community.React.sortKey`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byKey`, `Community.Receive.byMsg`, `Community.Receive.check`, `Community.Receive.childrenByKey`, `Community.Receive.instCodecBody`, `Community.Receive.rootsByKey`, `Community.Receive.sortKey`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.check`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.check`, `Community.Rename.current`, `Community.Rename.instCodecBody`, `Community.Rename.sortKey`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.all`, `Community.Request.check`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.all`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.byUser`, `Community.Root.check`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.all`, `Community.Secret.byKey`, `Community.Secret.check`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.byContentKey`, `Community.Wrap.byRecipient`, `Community.Wrap.check`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.abandoned.byRequest`, `Community.accepted.all`, `Community.admin.byUser`, `Community.admission.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.admission.byUser`, `Community.allowPeer`, `Community.approval.byRequest`, `Community.attachment.byMessage`, `Community.be64`, `Community.check`, `Community.chunk.byAttachment`, `Community.countCap`, `Community.counterOk`, `Community.cryptoSeal`, `Community.decWith`, `Community.deviceLive`, `Community.endpoint.all`, `Community.family`, `Community.instCodecBody`, `Community.instSortKeyFact`, `Community.isAdmin`, `Community.isBlank`, `Community.joining.all`, `Community.key.byCommunity`, `Community.key.byId`, `Community.keys`, `Community.kidOf`, `Community.live`, `Community.look`, `Community.maxFile`, `Community.maxSealedMeta`, `Community.message.all`, `Community.message.byAuthor`, `Community.message.byKey`, `Community.message.childrenByKey`, `Community.message.rootsByKey`, `Community.msgKey`, `Community.nameLook`, `Community.named.current`, `Community.orderOf`, `Community.prevMax`, `Community.profile.all`, `Community.profile.byLook`, `Community.profile.byUser`, `Community.react.byMessage`, `Community.react.byMessageEmoji`, `Community.recKey`, `Community.received.all`, `Community.received.byKey`, `Community.received.byMsg`, `Community.received.childrenByKey`, `Community.received.rootsByKey`, `Community.rels`, `Community.removal.byUser`, `Community.removals`, `Community.request.all`, `Community.scopeOf`, `Community.secret.all`, `Community.secret.byKey`, `Community.signedBy`, `Community.sortOf`, `Community.timeCap`, `Community.unremoved`, `Community.validate`, `Community.wrap.byContentKey`, `Community.wrap.byRecipient`, `Engine.Answer`, `Engine.Bytes`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Family`, `Engine.Family.fileKeys`, `Engine.Id`, `Engine.Key32`, `Engine.ListQ`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Pos`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Rel.query`, `Engine.Rel.read`, `Engine.Scope`, `Engine.SortKey`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.View`, `Engine.View.bind`, `Engine.View.instMonad`, `Engine.View.read`, `Engine.allValid`, `Engine.anyInvalid`, `Engine.instTickId`, `Engine.judge`, `Engine.keysOf`, `Engine.opKey`, `Engine.sha256`, `Merkle.B`, `Merkle.be64`, `Merkle.climb`, `Merkle.depthOf`, `Merkle.leaf`, `Merkle.nChunks`, `Merkle.node`, `Merkle.rootOf`, `Merkle.sliceLen`, `Merkle.sliceSize`, `Merkle.tagLeaf`, `Merkle.tagNode`, `Merkle.tagRoot`, `Merkle.verify`, `Text.inRange`, `Text.isInvisible`

</details>

## Connection.removal_reaches_session

<details><summary>Of the app: 542 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Fact`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Fact`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.receive`, `Community.Body.request`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.instCodecBody`, `Community.Chunk.sortKey`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.instCodecBody`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admission?`, `Community.Fact.endpoint?`, `Community.Fact.joining?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.secret?`, `Community.Grant.Body`, `Community.Grant.Fact`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Fact`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Fact`, `Community.Post.instCodecBody`, `Community.Post.sortKey`, `Community.Profile.Body`, `Community.Profile.Fact`, `Community.Profile.instCodecBody`, `Community.Profile.sortKey`, `Community.React.Body`, `Community.React.Fact`, `Community.React.instCodecBody`, `Community.React.sortKey`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byMsg`, `Community.Receive.instCodecBody`, `Community.Receive.sortKey`, `Community.Remove.Body`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Fact`, `Community.Rename.instCodecBody`, `Community.Rename.sortKey`, `Community.Request.Body`, `Community.Request.Fact`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Fact`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.instCodecBody`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.byKey`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.accepted.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.allowPeer`, `Community.be64`, `Community.better`, `Community.countCap`, `Community.decWith`, `Community.deviceLive`, `Community.deviceRemovals`, `Community.endpoint.all`, `Community.idLt`, `Community.instCodecBody`, `Community.instSortKeyFact`, `Community.joining.all`, `Community.live`, `Community.mine`, `Community.mkOp`, `Community.msgKey`, `Community.nodeKey`, `Community.pick`, `Community.recKey`, `Community.receipt`, `Community.receiptFor`, `Community.received.all`, `Community.received.byMsg`, `Community.removal.byUser`, `Community.removals`, `Community.removalsAt`, `Community.removalsOf`, `Community.secret.byKey`, `Community.sortOf`, `Community.standing`, `Community.timeCap`, `Community.topReceived`, `Community.unremoved`, `Community.waiting`, `Connection.B`, `Connection.Body`, `Connection.Body.connection`, `Connection.Body.dec`, `Connection.Body.decFrom`, `Connection.Body.enc`, `Connection.Body.encInto`, `Connection.Body.eph`, `Connection.Body.established`, `Connection.Body.given`, `Connection.Body.kind`, `Connection.Body.opened`, `Connection.Body.recv`, `Connection.Body.request`, `Connection.Body.send`, `Connection.Eph.Body`, `Connection.Eph.Fact`, `Connection.Eph.byOf`, `Connection.Eph.instCodecBody`, `Connection.Eph.op`, `Connection.Established.Body`, `Connection.Established.Fact`, `Connection.Established.all`, `Connection.Established.byConn`, `Connection.Established.instCodecBody`, `Connection.Established.op`, `Connection.F`, `Connection.Fact`, `Connection.Fact.connection?`, `Connection.Fact.eph?`, `Connection.Fact.established?`, `Connection.Fact.given?`, `Connection.Fact.opened?`, `Connection.Fact.recv?`, `Connection.Fact.request?`, `Connection.Fact.send?`, `Connection.Frame.ad`, `Connection.Frame.cid`, `Connection.Frame.open`, `Connection.Frame.seal`, `Connection.Frame.version`, `Connection.Given.Body`, `Connection.Given.Fact`, `Connection.Given.byConn`, `Connection.Given.instCodecBody`, `Connection.Given.op`, `Connection.Keys`, `Connection.Noise.Cipher`, `Connection.Noise.Session`, `Connection.Noise.Suite`, `Connection.Noise.Sym`, `Connection.Noise.Sym.decHash`, `Connection.Noise.Sym.encHash`, `Connection.Noise.Sym.mixHash`, `Connection.Noise.Sym.mixKey`, `Connection.Noise.Sym.one`, `Connection.Noise.Sym.split`, `Connection.Noise.Sym.start`, `Connection.Noise.Sym.two`, `Connection.Noise.protocol`, `Connection.Noise.read1`, `Connection.Noise.sent1`, `Connection.Noise.write1`, `Connection.Noise.write2`, `Connection.Opened.Body`, `Connection.Opened.Fact`, `Connection.Opened.all`, `Connection.Opened.byRequest`, `Connection.Opened.instCodecBody`, `Connection.Opened.op`, `Connection.Recv.Body`, `Connection.Recv.Fact`, `Connection.Recv.byOp`, `Connection.Recv.instCodecBody`, `Connection.Recv.op`, `Connection.Recv.sortKey`, `Connection.Reply.Body`, `Connection.Reply.Fact`, `Connection.Reply.byRequest`, `Connection.Reply.instCodecBody`, `Connection.Reply.op`, `Connection.Request.Body`, `Connection.Request.Fact`, `Connection.Request.byFrm`, `Connection.Request.byTo`, `Connection.Request.instCodecBody`, `Connection.Request.op`, `Connection.Send.Body`, `Connection.Send.Fact`, `Connection.Send.all`, `Connection.Send.instCodecBody`, `Connection.Send.op`, `Connection.allSessions`, `Connection.answerAll`, `Connection.answerOne`, `Connection.arrival`, `Connection.arrivedFrom`, `Connection.carrying`, `Connection.closing`, `Connection.connectedTo`, `Connection.connection.byRequest`, `Connection.count`, `Connection.decWith`, `Connection.deliverAll`, `Connection.delivers`, `Connection.dial`, `Connection.dialAll`, `Connection.dialOne`, `Connection.endpoints`, `Connection.eph.byOf`, `Connection.establishAll`, `Connection.establishConns`, `Connection.establishReqs`, `Connection.established.all`, `Connection.established.byConn`, `Connection.given.byConn`, `Connection.givenOn`, `Connection.heldV`, `Connection.hello`, `Connection.helloOf`, `Connection.hooks`, `Connection.instCodecBody`, `Connection.instSortKeyFact`, `Connection.joinOf`, `Connection.joinsOf`, `Connection.kept`, `Connection.lt`, `Connection.meV`, `Connection.mkOp`, `Connection.onArrival`, `Connection.onGiven`, `Connection.openAll`, `Connection.openEach`, `Connection.openFrame`, `Connection.openSessions`, `Connection.opened.all`, `Connection.opened.byRequest`, `Connection.outbox`, `Connection.peersOf`, `Connection.prologue`, `Connection.react`, `Connection.recv.byOp`, `Connection.request.byFrm`, `Connection.request.byTo`, `Connection.requestOf`, `Connection.resendConns`, `Connection.retired`, `Connection.retryKey`, `Connection.roomFor`, `Connection.rooms`, `Connection.roomsOf`, `Connection.roomsV`, `Connection.rows`, `Connection.sealFor`, `Connection.send.all`, `Connection.sessionKeys`, `Connection.sessionOf`, `Connection.sessions`, `Connection.sessionsOf`, `Connection.sortOf`, `Connection.trusts`, `Engine.Answer`, `Engine.Answer.lefts`, `Engine.Answer.rights`, `Engine.Bytes`, `Engine.Bytes.of?`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Family`, `Engine.Family.room`, `Engine.Family.shared`, `Engine.Fresh`, `Engine.Id`, `Engine.Key32`, `Engine.ListQ`, `Engine.Lists`, `Engine.Meter`, `Engine.Op`, `Engine.Op.bytes`, `Engine.Op.decode`, `Engine.Op.make`, `Engine.Pos`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Rel.query`, `Engine.Rel.read`, `Engine.Scope`, `Engine.SortKey`, `Engine.Store`, `Engine.Sync.Acts`, `Engine.Sync.Catalog`, `Engine.Sync.Claim`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.beginRound`, `Engine.Sync.Conn.carry`, `Engine.Sync.Conn.expireAsks`, `Engine.Sync.Conn.filed`, `Engine.Sync.Conn.filedGive`, `Engine.Sync.Conn.give`, `Engine.Sync.Conn.hotOf`, `Engine.Sync.Conn.notify`, `Engine.Sync.Conn.oldRound`, `Engine.Sync.Conn.onHold`, `Engine.Sync.Conn.onRbsr`, `Engine.Sync.Conn.onWant`, `Engine.Sync.Conn.open`, `Engine.Sync.Conn.owedAfter`, `Engine.Sync.Conn.queue`, `Engine.Sync.Conn.recv`, `Engine.Sync.Conn.retryIds`, `Engine.Sync.Conn.serveOwed`, `Engine.Sync.Conn.served`, `Engine.Sync.Conn.setRooms`, `Engine.Sync.Conn.shows`, `Engine.Sync.Conn.snap`, `Engine.Sync.Conn.start`, `Engine.Sync.Conn.tick`, `Engine.Sync.Conn.tickGive`, `Engine.Sync.Conn.walk`, `Engine.Sync.Conn.walkN`, `Engine.Sync.Conn.work`, `Engine.Sync.Effects`, `Engine.Sync.Effects.purge`, `Engine.Sync.Hooks`, `Engine.Sync.Index`, `Engine.Sync.Index.add`, `Engine.Sync.Index.items`, `Engine.Sync.Item`, `Engine.Sync.Key`, `Engine.Sync.Key.instDecidableLt`, `Engine.Sync.Key.instLT`, `Engine.Sync.Lane`, `Engine.Sync.Msg`, `Engine.Sync.Msg.ofOp`, `Engine.Sync.Msg.op`, `Engine.Sync.Node`, `Engine.Sync.Node.addr?`, `Engine.Sync.Node.afterActs`, `Engine.Sync.Node.apply`, `Engine.Sync.Node.close`, `Engine.Sync.Node.conn?`, `Engine.Sync.Node.drop`, `Engine.Sync.Node.endSession`, `Engine.Sync.Node.fanout`, `Engine.Sync.Node.finish`, `Engine.Sync.Node.flush`, `Engine.Sync.Node.follow`, `Engine.Sync.Node.heat`, `Engine.Sync.Node.hotIds`, `Engine.Sync.Node.onClose`, `Engine.Sync.Node.onFrame`, `Engine.Sync.Node.onSealed`, `Engine.Sync.Node.onTick`, `Engine.Sync.Node.onTickDirect`, `Engine.Sync.Node.onTickReserved`, `Engine.Sync.Node.onWrite`, `Engine.Sync.Node.open`, `Engine.Sync.Node.put`, `Engine.Sync.Node.recordGiven`, `Engine.Sync.Node.refresh`, `Engine.Sync.Node.reserved`, `Engine.Sync.Node.seal`, `Engine.Sync.Node.sealRetries`, `Engine.Sync.Node.sent`, `Engine.Sync.Node.serveOwed`, `Engine.Sync.Node.setAddr`, `Engine.Sync.Node.store`, `Engine.Sync.Node.sweep`, `Engine.Sync.Node.sweepAll`, `Engine.Sync.Node.write`, `Engine.Sync.Out`, `Engine.Sync.Params`, `Engine.Sync.Range`, `Engine.Sync.Range.has`, `Engine.Sync.Read`, `Engine.Sync.Read.map`, `Engine.Sync.Read.run`, `Engine.Sync.RetryOffer`, `Engine.Sync.RetryOrder.claim`, `Engine.Sync.RetryOrder.offered`, `Engine.Sync.RetryOrder.reconcile`, `Engine.Sync.RetryOrder.scan`, `Engine.Sync.RetryStore`, `Engine.Sync.RetryTicket`, `Engine.Sync.Room`, `Engine.Sync.Room.notices`, `Engine.Sync.Room.syncs`, `Engine.Sync.Route`, `Engine.Sync.Session`, `Engine.Sync.Session.close`, `Engine.Sync.Session.hearHello`, `Engine.Sync.Session.sayHello`, `Engine.Sync.Step`, `Engine.Sync.Step.pulse`, `Engine.Sync.Step.then`, `Engine.Sync.Sweep`, `Engine.Sync.Sweep.advance`, `Engine.Sync.Sweep.begin`, `Engine.Sync.Sweep.cost`, `Engine.Sync.Sweep.finish`, `Engine.Sync.Sweep.next`, `Engine.Sync.Sweep.offer`, `Engine.Sync.Sweep.run`, `Engine.Sync.Sweep.step`, `Engine.Sync.Sync`, `Engine.Sync.Turn`, `Engine.Sync.above`, `Engine.Sync.admitAsks`, `Engine.Sync.answer`, `Engine.Sync.authorize`, `Engine.Sync.bareTag`, `Engine.Sync.bundles`, `Engine.Sync.chunks`, `Engine.Sync.closureIds`, `Engine.Sync.closureOps`, `Engine.Sync.cutsOf`, `Engine.Sync.fetch`, `Engine.Sync.fp`, `Engine.Sync.holdsIn`, `Engine.Sync.holdsOf`, `Engine.Sync.ins`, `Engine.Sync.instAppendActs`, `Engine.Sync.instCodecClaim`, `Engine.Sync.instCodecKey`, `Engine.Sync.instCodecOption`, `Engine.Sync.instCodecRange`, `Engine.Sync.instDecidableEqKey`, `Engine.Sync.instDecidableEqLane`, `Engine.Sync.instDecidableEqRoute`, `Engine.Sync.isWire`, `Engine.Sync.kHave`, `Engine.Sync.kRbsr`, `Engine.Sync.kWant`, `Engine.Sync.keyOf`, `Engine.Sync.lbl`, `Engine.Sync.maxFrame`, `Engine.Sync.named`, `Engine.Sync.noteEpoch`, `Engine.Sync.num`, `Engine.Sync.opening`, `Engine.Sync.pick`, `Engine.Sync.pieceIds`, `Engine.Sync.pieces`, `Engine.Sync.queueClosure`, `Engine.Sync.remember`, `Engine.Sync.runLen`, `Engine.Sync.sealedTag`, `Engine.Sync.sends`, `Engine.Sync.serve`, `Engine.Sync.split`, `Engine.Sync.tagged`, `Engine.Sync.top`, `Engine.Sync.window`, `Engine.Sync.wireLane`, `Engine.Sync.within`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.View`, `Engine.View.bind`, `Engine.View.instMonad`, `Engine.View.liftL`, `Engine.View.read`, `Engine.View.run`, `Engine.has`, `Engine.ins`, `Engine.instCodecOp`, `Engine.instDecidableEqScope`, `Engine.instSortKeySum`, `Engine.instTickId`, `Engine.intake`, `Engine.intakeConn`, `Engine.sha256`

</details>

## Engine.Sync.recv_send

<details><summary>Of the app: 103 definitions</summary>

`Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.numEndM`, `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Meter`, `Engine.Op`, `Engine.Op.decode`, `Engine.Op.make`, `Engine.Scope`, `Engine.Store`, `Engine.Sync.Claim`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.beginRound`, `Engine.Sync.Conn.oldRound`, `Engine.Sync.Conn.onHold`, `Engine.Sync.Conn.onRbsr`, `Engine.Sync.Conn.onWant`, `Engine.Sync.Conn.recv`, `Engine.Sync.Conn.shows`, `Engine.Sync.Conn.snap`, `Engine.Sync.Conn.start`, `Engine.Sync.Index`, `Engine.Sync.Index.items`, `Engine.Sync.Item`, `Engine.Sync.Key`, `Engine.Sync.Key.instDecidableLt`, `Engine.Sync.Key.instLT`, `Engine.Sync.Msg`, `Engine.Sync.Msg.ofOp`, `Engine.Sync.Msg.op`, `Engine.Sync.Out`, `Engine.Sync.Params`, `Engine.Sync.Range`, `Engine.Sync.Range.has`, `Engine.Sync.Session`, `Engine.Sync.Session.hearHello`, `Engine.Sync.Step`, `Engine.Sync.above`, `Engine.Sync.admitAsks`, `Engine.Sync.answer`, `Engine.Sync.authorize`, `Engine.Sync.chunks`, `Engine.Sync.cutsOf`, `Engine.Sync.fp`, `Engine.Sync.holdsIn`, `Engine.Sync.instCodecClaim`, `Engine.Sync.instCodecKey`, `Engine.Sync.instCodecOption`, `Engine.Sync.instCodecRange`, `Engine.Sync.isWire`, `Engine.Sync.kHave`, `Engine.Sync.kRbsr`, `Engine.Sync.kWant`, `Engine.Sync.lbl`, `Engine.Sync.named`, `Engine.Sync.noteEpoch`, `Engine.Sync.opening`, `Engine.Sync.pick`, `Engine.Sync.pieceIds`, `Engine.Sync.pieces`, `Engine.Sync.remember`, `Engine.Sync.runLen`, `Engine.Sync.top`, `Engine.Sync.window`, `Engine.Sync.within`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.has`, `Engine.instCodecOp`, `Engine.instTickId`, `Engine.sha256`

</details>

## Connection.sealed_auth

<details><summary>Of the app: 260 definitions</summary>

`Community.Abandon.Fact`, `Community.Accept.Fact`, `Community.Approve.Fact`, `Community.Attach.Fact`, `Community.Chunk.Fact`, `Community.Chunk.sortKey`, `Community.ContentKey.Fact`, `Community.Endpoint.Fact`, `Community.Fact`, `Community.Grant.Fact`, `Community.Invitation.Fact`, `Community.Joining.Fact`, `Community.Key`, `Community.Post.Fact`, `Community.Post.sortKey`, `Community.Profile.Fact`, `Community.Profile.sortKey`, `Community.React.Fact`, `Community.React.sortKey`, `Community.Receive.Fact`, `Community.Receive.sortKey`, `Community.Remove.Fact`, `Community.Rename.Fact`, `Community.Rename.sortKey`, `Community.Request.Fact`, `Community.Root.Fact`, `Community.Secret.Fact`, `Community.Wrap.Fact`, `Community.be64`, `Community.countCap`, `Community.instSortKeyFact`, `Community.msgKey`, `Community.recKey`, `Community.sortOf`, `Community.timeCap`, `Connection.B`, `Connection.Eph.Fact`, `Connection.Established.Fact`, `Connection.Established.byConn`, `Connection.F`, `Connection.Fact`, `Connection.Fact.established?`, `Connection.Frame.ad`, `Connection.Frame.cid`, `Connection.Frame.open`, `Connection.Frame.version`, `Connection.Given.Fact`, `Connection.Keys`, `Connection.Noise.Suite`, `Connection.Opened.Fact`, `Connection.Recv.Fact`, `Connection.Recv.sortKey`, `Connection.Reply.Fact`, `Connection.Request.Fact`, `Connection.Send.Fact`, `Connection.established.byConn`, `Connection.instSortKeyFact`, `Connection.openFrame`, `Connection.rows`, `Connection.sessionKeys`, `Connection.sortOf`, `Engine.Answer`, `Engine.Answer.rights`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.numEndM`, `Engine.Family`, `Engine.Family.room`, `Engine.Family.shared`, `Engine.Id`, `Engine.ListQ`, `Engine.Lists`, `Engine.Meter`, `Engine.Op`, `Engine.Op.bytes`, `Engine.Op.decode`, `Engine.Op.make`, `Engine.Pos`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Rel.query`, `Engine.Scope`, `Engine.SortKey`, `Engine.Store`, `Engine.Sync.Acts`, `Engine.Sync.Catalog`, `Engine.Sync.Claim`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.beginRound`, `Engine.Sync.Conn.carry`, `Engine.Sync.Conn.filed`, `Engine.Sync.Conn.filedGive`, `Engine.Sync.Conn.give`, `Engine.Sync.Conn.hotOf`, `Engine.Sync.Conn.notify`, `Engine.Sync.Conn.oldRound`, `Engine.Sync.Conn.onHold`, `Engine.Sync.Conn.onRbsr`, `Engine.Sync.Conn.onWant`, `Engine.Sync.Conn.open`, `Engine.Sync.Conn.owedAfter`, `Engine.Sync.Conn.queue`, `Engine.Sync.Conn.recv`, `Engine.Sync.Conn.serveOwed`, `Engine.Sync.Conn.served`, `Engine.Sync.Conn.setRooms`, `Engine.Sync.Conn.shows`, `Engine.Sync.Conn.snap`, `Engine.Sync.Conn.start`, `Engine.Sync.Effects`, `Engine.Sync.Effects.purge`, `Engine.Sync.Hooks`, `Engine.Sync.Index`, `Engine.Sync.Index.add`, `Engine.Sync.Index.items`, `Engine.Sync.Item`, `Engine.Sync.Key`, `Engine.Sync.Key.instDecidableLt`, `Engine.Sync.Key.instLT`, `Engine.Sync.Lane`, `Engine.Sync.Msg`, `Engine.Sync.Msg.ofOp`, `Engine.Sync.Msg.op`, `Engine.Sync.Node`, `Engine.Sync.Node.addr?`, `Engine.Sync.Node.apply`, `Engine.Sync.Node.close`, `Engine.Sync.Node.conn?`, `Engine.Sync.Node.drop`, `Engine.Sync.Node.endSession`, `Engine.Sync.Node.fanout`, `Engine.Sync.Node.finish`, `Engine.Sync.Node.flush`, `Engine.Sync.Node.follow`, `Engine.Sync.Node.hotIds`, `Engine.Sync.Node.onFrame`, `Engine.Sync.Node.onSealed`, `Engine.Sync.Node.open`, `Engine.Sync.Node.put`, `Engine.Sync.Node.recordGiven`, `Engine.Sync.Node.refresh`, `Engine.Sync.Node.seal`, `Engine.Sync.Node.sealRetries`, `Engine.Sync.Node.sent`, `Engine.Sync.Node.serveOwed`, `Engine.Sync.Node.setAddr`, `Engine.Sync.Node.store`, `Engine.Sync.Node.write`, `Engine.Sync.Out`, `Engine.Sync.Params`, `Engine.Sync.Range`, `Engine.Sync.Range.has`, `Engine.Sync.Read`, `Engine.Sync.Read.map`, `Engine.Sync.Read.run`, `Engine.Sync.RetryOffer`, `Engine.Sync.RetryStore`, `Engine.Sync.RetryTicket`, `Engine.Sync.Room`, `Engine.Sync.Room.notices`, `Engine.Sync.Room.syncs`, `Engine.Sync.Route`, `Engine.Sync.Session`, `Engine.Sync.Session.hearHello`, `Engine.Sync.Session.sayHello`, `Engine.Sync.Step`, `Engine.Sync.Step.then`, `Engine.Sync.Sweep`, `Engine.Sync.Sync`, `Engine.Sync.Turn`, `Engine.Sync.above`, `Engine.Sync.admitAsks`, `Engine.Sync.answer`, `Engine.Sync.authorize`, `Engine.Sync.bareTag`, `Engine.Sync.bundles`, `Engine.Sync.chunks`, `Engine.Sync.closureIds`, `Engine.Sync.closureOps`, `Engine.Sync.cutsOf`, `Engine.Sync.fetch`, `Engine.Sync.fp`, `Engine.Sync.holdsIn`, `Engine.Sync.holdsOf`, `Engine.Sync.ins`, `Engine.Sync.instAppendActs`, `Engine.Sync.instCodecClaim`, `Engine.Sync.instCodecKey`, `Engine.Sync.instCodecOption`, `Engine.Sync.instCodecRange`, `Engine.Sync.instDecidableEqKey`, `Engine.Sync.instDecidableEqLane`, `Engine.Sync.instDecidableEqRoute`, `Engine.Sync.isWire`, `Engine.Sync.kHave`, `Engine.Sync.kRbsr`, `Engine.Sync.kWant`, `Engine.Sync.keyOf`, `Engine.Sync.lbl`, `Engine.Sync.named`, `Engine.Sync.noteEpoch`, `Engine.Sync.num`, `Engine.Sync.opening`, `Engine.Sync.pick`, `Engine.Sync.pieceIds`, `Engine.Sync.pieces`, `Engine.Sync.queueClosure`, `Engine.Sync.remember`, `Engine.Sync.runLen`, `Engine.Sync.sealedTag`, `Engine.Sync.sends`, `Engine.Sync.serve`, `Engine.Sync.split`, `Engine.Sync.tagged`, `Engine.Sync.top`, `Engine.Sync.window`, `Engine.Sync.wireLane`, `Engine.Sync.within`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.has`, `Engine.ins`, `Engine.instCodecOp`, `Engine.instDecidableEqScope`, `Engine.instSortKeySum`, `Engine.instTickId`, `Engine.intake`, `Engine.intakeConn`, `Engine.sha256`

</details>

## Connection.Noise.Symbolic.kk_secret

<details><summary>Of the app: 18 definitions</summary>

`Connection.Noise.Cipher`, `Connection.Noise.Session`, `Connection.Noise.Suite`, `Connection.Noise.Sym`, `Connection.Noise.Sym.decHash`, `Connection.Noise.Sym.encHash`, `Connection.Noise.Sym.mixHash`, `Connection.Noise.Sym.mixKey`, `Connection.Noise.Sym.one`, `Connection.Noise.Sym.split`, `Connection.Noise.Sym.start`, `Connection.Noise.Sym.two`, `Connection.Noise.protocol`, `Connection.Noise.read1`, `Connection.Noise.read2`, `Connection.Noise.sent1`, `Connection.Noise.write1`, `Connection.Noise.write2`

</details>

## Connection.Noise.Symbolic.kk_authentic

<details><summary>Of the app: 18 definitions</summary>

`Connection.Noise.Cipher`, `Connection.Noise.Session`, `Connection.Noise.Suite`, `Connection.Noise.Sym`, `Connection.Noise.Sym.decHash`, `Connection.Noise.Sym.encHash`, `Connection.Noise.Sym.mixHash`, `Connection.Noise.Sym.mixKey`, `Connection.Noise.Sym.one`, `Connection.Noise.Sym.split`, `Connection.Noise.Sym.start`, `Connection.Noise.Sym.two`, `Connection.Noise.protocol`, `Connection.Noise.read1`, `Connection.Noise.read2`, `Connection.Noise.sent1`, `Connection.Noise.write1`, `Connection.Noise.write2`

</details>

## Engine.same_ops_same_verdicts

<details><summary>Of the app: 33 definitions</summary>

`Engine.Codec`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Family`, `Engine.Id`, `Engine.Meter`, `Engine.Op`, `Engine.Scope`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.has`, `Engine.instTickId`, `Engine.sha256`

</details>

## Community.display_agrees

<details><summary>Of the app: 306 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Fact`, `Community.Abandon.byJoining`, `Community.Abandon.byRequest`, `Community.Abandon.check`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Fact`, `Community.Accept.all`, `Community.Accept.check`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Fact`, `Community.Admit.check`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.byRequest`, `Community.Approve.check`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.byMessage`, `Community.Attach.check`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.community`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.isLocal`, `Community.Body.post`, `Community.Body.tag`, `Community.Chunk.Body`, `Community.Chunk.Fact`, `Community.Chunk.byAttachment`, `Community.Chunk.check`, `Community.Chunk.instCodecBody`, `Community.ContentKey.Body`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.byId`, `Community.ContentKey.check`, `Community.ContentKey.instCodecBody`, `Community.Crypto`, `Community.Endpoint.Body`, `Community.Endpoint.Fact`, `Community.Endpoint.all`, `Community.Endpoint.check`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.abandoned?`, `Community.Fact.accepted?`, `Community.Fact.admin?`, `Community.Fact.admission?`, `Community.Fact.approval?`, `Community.Fact.attachment?`, `Community.Fact.chunk?`, `Community.Fact.endpoint?`, `Community.Fact.isLocal`, `Community.Fact.joining?`, `Community.Fact.key?`, `Community.Fact.message?`, `Community.Fact.named?`, `Community.Fact.profile?`, `Community.Fact.react?`, `Community.Fact.received?`, `Community.Fact.removal?`, `Community.Fact.request?`, `Community.Fact.secret?`, `Community.Fact.wrap?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.byUser`, `Community.Grant.check`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.check`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Fact`, `Community.Joining.all`, `Community.Joining.check`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.all`, `Community.Post.byAuthor`, `Community.Post.byKey`, `Community.Post.check`, `Community.Post.childrenByKey`, `Community.Post.instCodecBody`, `Community.Post.rootsByKey`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.all`, `Community.Profile.byLook`, `Community.Profile.byUser`, `Community.Profile.check`, `Community.Profile.instCodecBody`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.byMessage`, `Community.React.byMessageEmoji`, `Community.React.check`, `Community.React.instCodecBody`, `Community.Receive.Body`, `Community.Receive.Fact`, `Community.Receive.all`, `Community.Receive.byKey`, `Community.Receive.byMsg`, `Community.Receive.check`, `Community.Receive.childrenByKey`, `Community.Receive.instCodecBody`, `Community.Receive.rootsByKey`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Remove.check`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.check`, `Community.Rename.current`, `Community.Rename.instCodecBody`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.all`, `Community.Request.check`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.all`, `Community.Root.byDevice`, `Community.Root.byKey`, `Community.Root.byUser`, `Community.Root.check`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Fact`, `Community.Secret.all`, `Community.Secret.byKey`, `Community.Secret.check`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Fact`, `Community.Wrap.byContentKey`, `Community.Wrap.byRecipient`, `Community.Wrap.check`, `Community.Wrap.instCodecBody`, `Community.abandoned.byJoining`, `Community.abandoned.byRequest`, `Community.accepted.all`, `Community.admin.byUser`, `Community.admission.all`, `Community.admission.byDevice`, `Community.admission.byKey`, `Community.admission.byUser`, `Community.approval.byRequest`, `Community.attachment.byMessage`, `Community.be64`, `Community.check`, `Community.chunk.byAttachment`, `Community.countCap`, `Community.counterOk`, `Community.cryptoSeal`, `Community.decWith`, `Community.endpoint.all`, `Community.family`, `Community.instCodecBody`, `Community.isAdmin`, `Community.isBlank`, `Community.joining.all`, `Community.key.byCommunity`, `Community.key.byId`, `Community.keys`, `Community.kidOf`, `Community.look`, `Community.maxFile`, `Community.maxSealedMeta`, `Community.message.all`, `Community.message.byAuthor`, `Community.message.byKey`, `Community.message.childrenByKey`, `Community.message.rootsByKey`, `Community.msgKey`, `Community.nameLook`, `Community.named.current`, `Community.orderOf`, `Community.prevMax`, `Community.profile.all`, `Community.profile.byLook`, `Community.profile.byUser`, `Community.react.byMessage`, `Community.react.byMessageEmoji`, `Community.recKey`, `Community.received.all`, `Community.received.byKey`, `Community.received.byMsg`, `Community.received.childrenByKey`, `Community.received.rootsByKey`, `Community.rels`, `Community.removal.byUser`, `Community.request.all`, `Community.scopeOf`, `Community.secret.all`, `Community.secret.byKey`, `Community.signedBy`, `Community.timeCap`, `Community.validate`, `Community.wrap.byContentKey`, `Community.wrap.byRecipient`, `Engine.Bytes`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.decode`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Family`, `Engine.Id`, `Engine.Key32`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Pos`, `Engine.Pos.cmp`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Scope`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.allValid`, `Engine.anyInvalid`, `Engine.bcmp`, `Engine.bcmpFrom`, `Engine.instTickId`, `Engine.judge`, `Engine.keysOf`, `Engine.sha256`, `Merkle.B`, `Merkle.be64`, `Merkle.climb`, `Merkle.depthOf`, `Merkle.leaf`, `Merkle.nChunks`, `Merkle.node`, `Merkle.rootOf`, `Merkle.sliceLen`, `Merkle.sliceSize`, `Merkle.tagLeaf`, `Merkle.tagNode`, `Merkle.tagRoot`, `Merkle.verify`, `Text.inRange`, `Text.isInvisible`

</details>

## Cover.covered

<details><summary>Of the app: 3 definitions</summary>

`Cover.Px`, `Cover.find`, `Cover.seen`

</details>

## NavLaws.back_open

<details><summary>Of the app: 223 definitions</summary>

`App.ImgKey`, `App.Io`, `App.PageId`, `App.PageIn`, `App.Presentation.Entry`, `App.Presentation.Queue`, `App.Presentation.capacity`, `App.PresentationCandidate`, `App.RowPixels`, `App.RowSt`, `App.SheetSt`, `App.St`, `App.St.nav`, `App.St.withNav`, `App.backSt`, `App.instDecidableEqPageId`, `App.openSt`, `Chaos.Me`, `ClumpList.Window`, `Community.Abandon.Fact`, `Community.Accept.Fact`, `Community.Approve.Fact`, `Community.Attach.Fact`, `Community.Chunk.Fact`, `Community.ContentKey.Fact`, `Community.Device`, `Community.Device.ofSeed`, `Community.Endpoint.Fact`, `Community.Fact`, `Community.Grant.Fact`, `Community.Invitation.Fact`, `Community.Invite`, `Community.Joining.Fact`, `Community.Key`, `Community.Post.Fact`, `Community.Profile.Fact`, `Community.React.Fact`, `Community.Receive.Fact`, `Community.Remove.Fact`, `Community.Rename.Fact`, `Community.Request.Fact`, `Community.Root.Fact`, `Community.Secret.Fact`, `Community.Wrap.Fact`, `Community.Write`, `Composer.Chip`, `Data.Ans`, `Data.Entry`, `Data.Job`, `Data.Live`, `Data.Pending`, `Data.Q`, `Data.Writer`, `Data.WriterQueue`, `Data.instBEqQ`, `Data.instBEqQ.beq`, `Data.instHashableQ`, `Data.instHashableQ.hash`, `Demand.Need`, `Demand.Owner`, `Demand.Plan`, `Demand.Ticket`, `Editor.Io`, `Editor.State`, `Emoji.Entry`, `Emoji.Set`, `Engine.Answer`, `Engine.Codec`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Crypto.edKeypair`, `Engine.Db`, `Engine.DbPointed`, `Engine.End`, `Engine.Filing`, `Engine.Id`, `Engine.ListQ`, `Engine.Meter`, `Engine.Op`, `Engine.Pos`, `Engine.Slots`, `Engine.Subs`, `Engine.Sync.Event`, `Engine.Sync.Inbox.Priority.Slot`, `Engine.Sync.Inbox.Priority.State`, `Engine.Sync.Ingress.Hub`, `Engine.Sync.Ingress.Registry`, `Engine.Sync.Ingress.State`, `Engine.Sync.JobOwners`, `Engine.Sync.NativeJob`, `Engine.Sync.Runner`, `Engine.Sync.Slots`, `Engine.Sync.StopFlag`, `Engine.Sync.TurnCounters`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Win`, `Engine.instBEqListQ`, `Engine.instBEqListQ.beq`, `Engine.instHashableListQ`, `Engine.instHashableListQ.hash`, `Engine.instTickId`, `Engine.sha256`, `FileImage.Key`, `Font.Font`, `Geometry.Geom`, `Glyphs.Set`, `Hold.MessageCache`, `Hold.MessageKey`, `Hold.MessageKey.rows`, `Hold.MessageKey.state`, `Hold.MessageTile`, `Hold.St`, `Hold.messageLine`, `Hold.period`, `Hover.Context`, `Hover.Point`, `Image.Src`, `Input.Context`, `Input.Point`, `Input.Press`, `Input.State`, `Input.Touch`, `Kinds.Accepted.Key`, `Kinds.Accepted.Me`, `Kinds.Request.Data`, `Lifecycle.Checkpoint`, `Lifecycle.Mount`, `Live.Board`, `Live.Ver`, `Nav.Nav`, `Nav.back`, `Nav.go`, `Nav.under`, `Noto.Cached`, `Noto.Ref`, `Noto.Set`, `Pages.Act`, `Pages.Asking`, `Pages.Box`, `Pages.Page`, `Pages.PageOf`, `Paint.Bitmap`, `Paint.Color`, `Paint.Stroke`, `Paint.b8`, `Paint.blendText`, `Paint.cover`, `Paint.g8`, `Paint.getPx`, `Paint.mixC`, `Paint.r8`, `Paint.setPx`, `Palette.Token`, `Palette.color`, `Photo.Request`, `Raster.Key`, `Raster.RowPaint.Flight`, `Raster.RowPaint.Stamp`, `Reader.Act`, `Reader.RM`, `Reader.Shared`, `Reader.St`, `Reader.Val`, `Reader.Want`, `Reader.Worker`, `Reader.instDecidableEqWant`, `Reader.instHashableWant`, `Reader.instHashableWant.hash`, `Remove.Step`, `Row.Box`, `Row.Dim`, `Row.Dim.avatar`, `Row.Dim.pad`, `Row.Dim.px`, `Row.Dim.textX`, `Row.Layout`, `Row.Pic`, `Row.RowData`, `Row.Tally`, `Safe.Input`, `Safe.Insets`, `Session.Show`, `Sheet.Item`, `Surface.Frame`, `Surface.Rect`, `Surface.compose`, `Text.Line`, `Text.Placed`, `Theme.Setting`, `Theme.State`, `Theme.Value`, `Ttf.Cmap`, `Ttf.Entry`, `Ttf.Face`, `Ttf.Mapping`, `Ttf.Memo.Source`, `Work.Action`, `Work.Handle`, `Work.Job`, `Work.Pool`, `Work.State`, `Work.Stats`, `Hold.capsule`

</details>

## Switch.select_tapped_dedupe

<details><summary>Of the app: 9 definitions</summary>

`Community.Device`, `Community.Device.ofSeed`, `Community.Key`, `Engine.Crypto.edKeypair`, `Engine.Id`, `Kinds.Accepted.Me`, `Kinds.Accepted.dedupe`, `Kinds.Accepted.dedupeBy`, `Kinds.Accepted.select`

</details>

## Community.approveReq_ops

<details><summary>Of the app: 181 definitions</summary>

`Community.Abandon.Body`, `Community.Abandon.Body.unsigned`, `Community.Abandon.Fact`, `Community.Abandon.instCodecBody`, `Community.Accept.Body`, `Community.Accept.Body.unsigned`, `Community.Accept.Fact`, `Community.Accept.instCodecBody`, `Community.Admit.Body`, `Community.Admit.Body.unsigned`, `Community.Admit.instCodecBody`, `Community.Approve.Body`, `Community.Approve.Body.unsigned`, `Community.Approve.Fact`, `Community.Approve.instCodecBody`, `Community.Attach.Body`, `Community.Attach.Body.unsigned`, `Community.Attach.Fact`, `Community.Attach.instCodecBody`, `Community.B`, `Community.Body`, `Community.Body.admit`, `Community.Body.approve`, `Community.Body.dec`, `Community.Body.decFrom`, `Community.Body.enc`, `Community.Body.encInto`, `Community.Body.tag`, `Community.Body.unsigned`, `Community.Body.wrap`, `Community.Chunk.Body`, `Community.Chunk.Body.unsigned`, `Community.Chunk.Fact`, `Community.Chunk.instCodecBody`, `Community.ContentKey.Body`, `Community.ContentKey.Body.unsigned`, `Community.ContentKey.Fact`, `Community.ContentKey.byCommunity`, `Community.ContentKey.instCodecBody`, `Community.Device`, `Community.Endpoint.Body`, `Community.Endpoint.Body.unsigned`, `Community.Endpoint.Fact`, `Community.Endpoint.instCodecBody`, `Community.Fact`, `Community.Fact.key?`, `Community.Grant.Body`, `Community.Grant.Body.unsigned`, `Community.Grant.Fact`, `Community.Grant.instCodecBody`, `Community.Invitation.Body`, `Community.Invitation.Body.unsigned`, `Community.Invitation.Fact`, `Community.Invitation.instCodecBody`, `Community.Joining.Body`, `Community.Joining.Body.unsigned`, `Community.Joining.Fact`, `Community.Joining.instCodecBody`, `Community.Key`, `Community.Post.Body`, `Community.Post.Body.unsigned`, `Community.Post.Fact`, `Community.Post.instCodecBody`, `Community.Profile.Body`, `Community.Profile.Body.unsigned`, `Community.Profile.Fact`, `Community.Profile.instCodecBody`, `Community.React.Body`, `Community.React.Body.unsigned`, `Community.React.Fact`, `Community.React.instCodecBody`, `Community.Receive.Body`, `Community.Receive.Body.unsigned`, `Community.Receive.Fact`, `Community.Receive.instCodecBody`, `Community.Remove.Body`, `Community.Remove.Body.unsigned`, `Community.Remove.Fact`, `Community.Remove.instCodecBody`, `Community.Rename.Body`, `Community.Rename.Body.unsigned`, `Community.Rename.Fact`, `Community.Rename.instCodecBody`, `Community.Request.Body`, `Community.Request.Body.unsigned`, `Community.Request.Fact`, `Community.Request.instCodecBody`, `Community.Root.Body`, `Community.Root.Body.unsigned`, `Community.Root.Fact`, `Community.Root.instCodecBody`, `Community.Seal`, `Community.Secret.Body`, `Community.Secret.Body.unsigned`, `Community.Secret.Fact`, `Community.Secret.instCodecBody`, `Community.Wrap.Body`, `Community.Wrap.Body.unsigned`, `Community.Wrap.Fact`, `Community.Wrap.instCodecBody`, `Community.Write`, `Community.admit`, `Community.approve`, `Community.approveReq`, `Community.box`, `Community.boxKey`, `Community.cryptoSeal`, `Community.decWith`, `Community.instCodecBody`, `Community.key.byCommunity`, `Community.kidOf`, `Community.mkOp`, `Community.sig`, `Community.toSign`, `Community.wrap`, `Community.wrapKey`, `Community.zeros24`, `Engine.Answer`, `Engine.Bytes`, `Engine.Bytes.of?`, `Engine.Bytes.zeros`, `Engine.Codec`, `Engine.Codec.byteAt`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decFromAs`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decNatFrom`, `Engine.Codec.decNatFromM`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.digits`, `Engine.Codec.digitsM`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instBool`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instNat`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Codec.instUnit`, `Engine.Codec.numEndM`, `Engine.Codec.tagged`, `Engine.Crypto.edSign`, `Engine.Crypto.x25519`, `Engine.Crypto.x25519Base`, `Engine.Crypto.xchachaOpen`, `Engine.Crypto.xchachaSeal`, `Engine.Id`, `Engine.Key32`, `Engine.ListQ`, `Engine.Meter`, `Engine.Nonce24`, `Engine.Op`, `Engine.Op.make`, `Engine.Pos`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Rel.query`, `Engine.Rel.read`, `Engine.Tick`, `Engine.Tick.free`, `Engine.View`, `Engine.View.bind`, `Engine.View.instMonad`, `Engine.View.read`, `Engine.instTickId`, `Engine.opKey`, `Engine.sha256`

</details>

## Engine.ingest_costs

<details><summary>Of the app: 32 definitions</summary>

`Engine.Codec`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instProd`, `Engine.Codec.instUInt8`, `Engine.Id`, `Engine.Meter`, `Engine.Op`, `Engine.Store`, `Engine.Tick`, `Engine.Tick.free`, `Engine.Verdict`, `Engine.ingest`, `Engine.instTickId`, `Engine.sha256`

</details>

## PeopleLaws.deviceCut_removal

<details><summary>Of the app: 83 definitions</summary>

`Community.Abandon.Fact`, `Community.Accept.Fact`, `Community.Approve.Fact`, `Community.Attach.Fact`, `Community.Chunk.Fact`, `Community.Chunk.sortKey`, `Community.ContentKey.Fact`, `Community.Endpoint.Fact`, `Community.Fact`, `Community.Fact.admission?`, `Community.Fact.removal?`, `Community.Grant.Fact`, `Community.Invitation.Fact`, `Community.Joining.Fact`, `Community.Key`, `Community.Post.Fact`, `Community.Post.sortKey`, `Community.Profile.Fact`, `Community.Profile.sortKey`, `Community.React.Fact`, `Community.React.sortKey`, `Community.Receive.Fact`, `Community.Receive.sortKey`, `Community.Remove.Fact`, `Community.Remove.byUser`, `Community.Rename.Fact`, `Community.Rename.sortKey`, `Community.Request.Fact`, `Community.Root.Fact`, `Community.Root.byDevice`, `Community.Secret.Fact`, `Community.Wrap.Fact`, `Community.admission.byDevice`, `Community.be64`, `Community.countCap`, `Community.deviceCut`, `Community.instSortKeyFact`, `Community.msgKey`, `Community.recKey`, `Community.removal.byUser`, `Community.removals`, `Community.sortOf`, `Community.timeCap`, `Community.unremoved`, `Engine.Answer`, `Engine.Codec`, `Engine.Codec.contDigitsInto`, `Engine.Codec.contDigitsLoop`, `Engine.Codec.decBytesFrom`, `Engine.Codec.decBytesFromM`, `Engine.Codec.decBytesL`, `Engine.Codec.decLenFromM`, `Engine.Codec.decListF`, `Engine.Codec.decListFrom`, `Engine.Codec.decNat`, `Engine.Codec.decPair`, `Engine.Codec.decPairFrom`, `Engine.Codec.encBytesL`, `Engine.Codec.encList`, `Engine.Codec.encListInto`, `Engine.Codec.encNat`, `Engine.Codec.encNatInto`, `Engine.Codec.encode`, `Engine.Codec.instByteArray`, `Engine.Codec.instList`, `Engine.Codec.instProd`, `Engine.Id`, `Engine.ListQ`, `Engine.Meter`, `Engine.Pos`, `Engine.Rel`, `Engine.Rel.comap`, `Engine.Rel.key`, `Engine.Rel.query`, `Engine.Rel.read`, `Engine.SortKey`, `Engine.Tick`, `Engine.Tick.free`, `Engine.View`, `Engine.View.bind`, `Engine.View.instMonad`, `Engine.View.read`, `Engine.instTickId`

</details>

## The other laws' surfaces

#### Engine.Op.id_decode

Named in the statement: `Engine.Id`, `Engine.Op`, `Engine.Op.decode`, `Engine.sha256`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: none. Bridged: none.

#### Remove.writes_only_after_two

Named in the statement: `Engine.Id`, `Remove.Ev`, `Remove.Step`, `Remove.step`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Text.wrap_keeps

Named in the statement: `Font.Font`, `Text.ns`, `Text.wrapL`.

Spec-only, to review: definitions: `Text.ns`.

Assumed: none. Bridged: none.

#### Community.message_authorized

Named in the statement: `Community.Body`, `Community.Body.post`, `Community.Crypto`, `Community.Fact.admission`, `Community.Fact.message`, `Community.Key`, `Community.V`, `Community.instCodecBody`, `Community.signed`, `Engine.Codec.decode`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.message`, `Engine.specAt`.

Assumed: none. Bridged: `Community.signed` (by `Community.signed_eq`).

#### Community.removal_cuts_off

Named in the statement: `Community.Admitted`, `Community.Crypto`, `Community.Fact`, `Community.Key`, `Community.Removed`, `Community.allowPeer`, `Community.family`, `Community.instSortKeyFact`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Engine.View.eval`.

Spec-only, to review: predicates: `Community.Admitted`, `Community.Removed`, `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.removal`, `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Community.valid_stays

Named in the statement: `Community.Crypto`, `Community.Fact`, `Community.V`, `Engine.Extends`, `Engine.Id`, `Engine.Op`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Extends`, `Engine.Spec`; definitions: `Engine.specAt`.

Assumed: none. Bridged: none.

#### Connection.removed_gets_only_notice

Named in the statement: `Community.Fact`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.LiveIn`, `Connection.NoticeOnly`, `Connection.Refused`, `Connection.instSortKeyFact`, `Connection.roomsV`, `Engine.DB`, `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.carry`, `Engine.Sync.Conn.filedGive`, `Engine.Sync.Conn.open`, `Engine.Sync.Conn.recv`, `Engine.Sync.Conn.tickGive`, `Engine.Sync.Index`, `Engine.Sync.Room`, `Engine.Sync.Step`, `Engine.Sync.isWire`, `Engine.View.eval`, `Engine.instMonadModel`, `Engine.instSortKeySum`, `Engine.modelStore`.

Spec-only, to review: predicates: `Connection.LiveIn`, `Connection.NoticeOnly`, `Connection.Owed`, `Connection.Refused`, `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.ReachIn`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.eval`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### Engine.Sync.entry_fresh

Named in the statement: `Engine.Sync.Effects`, `Engine.Sync.Entry`, `Engine.Sync.FramesOk`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.Moves`, `Engine.Sync.Node`, `Engine.Sync.ReadOnly`, `Engine.Sync.Sync`, `Engine.Sync.instMonadHeldM`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Entry`, `Engine.Sync.FramesBy`, `Engine.Sync.FramesOk`, `Engine.Sync.Key.lt`, `Engine.Sync.Move`, `Engine.Sync.Moves`, `Engine.Sync.ReadOnly`, `Engine.Sync.Reads`, `Engine.Sync.Sent`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Engine.Sync.offer_shared

Named in the statement: `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.filed`, `Engine.Sync.Conn.walk`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.Msg.op`, `Engine.Sync.Step`, `Engine.Sync.holdsOf`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.has`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.lift`, `Engine.modelStore`. Bridged: none.

#### Engine.Sync.recv_take

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.recv`, `Engine.Sync.Index`, `Engine.Sync.Step`, `Engine.Sync.Takeable`, `Engine.instMonadModel`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.Sync.Takeable`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Engine.Sync.sealed_unopened

Named in the statement: `Engine.Id`, `Engine.Sync.Effects`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.Node`, `Engine.Sync.Node.onFrame`, `Engine.Sync.RetryTicket`, `Engine.Sync.Sync`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Engine.Codec.encode_decode

Named in the statement: `Engine.Codec`, `Engine.Codec.decode`, `Engine.Codec.encode`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: none. Bridged: none.

#### Engine.drain_bounded

Named in the statement: `Engine.DB`, `Engine.Distinct`, `Engine.Family`, `Engine.Id`, `Engine.Op`, `Engine.Reach`, `Engine.budget`, `Engine.drainS`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Reach`.

Assumed: `Engine.DB`, `Engine.DB.empty`, `Engine.Distinct`, `Engine.budget`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`), `Engine.stepS` (by `Engine.run_step`).

#### Engine.ingest_twice

Named in the statement: `Engine.DB`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.ingest`, `Engine.instMonadModel`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Engine.purge_shared

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Family.room`, `Engine.Id`, `Engine.Op`, `Engine.purgeS`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`. Bridged: `Engine.purgeS` (by `Engine.run_purge`).

#### Engine.status_iff_spec

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Id`, `Engine.Inv`, `Engine.Spec`, `Engine.Verdict`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: none.

#### Community.chunk_is_slice

Named in the statement: `Community.Body`, `Community.Body.chunk`, `Community.ChunkSound`, `Community.Crypto`, `Community.Fact`, `Community.Fact.chunk`, `Community.check`, `Engine.Id`, `Engine.Op`, `Engine.sha256`, `Merkle.B`, `Merkle.fileRoot`, `Merkle.proof`, `Merkle.slices`.

Spec-only, to review: predicates: `Engine.Codec.At`; definitions: `Community.Fact.chunk`, `Merkle.slices`.

Assumed: `Community.ChunkSound`. Bridged: none.

#### Connection.bare_takes_only_join

Named in the statement: `Community.Body`, `Community.Body.request`, `Community.Crypto`, `Community.Fact`, `Community.instCodecBody`, `Community.instSortKeyFact`, `Connection.B`, `Connection.F`, `Connection.Fact`, `Connection.Fact.opened`, `Connection.Keys`, `Connection.instSortKeyFact`, `Connection.node`, `Connection.opened.all`, `Connection.react`, `Engine.Codec.decode`, `Engine.DB`, `Engine.Family.room`, `Engine.Fresh`, `Engine.Id`, `Engine.Model`, `Engine.Model.run`, `Engine.Op`, `Engine.Op.bytes`, `Engine.Pos`, `Engine.Rel.query`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.instMonadModel`, `Engine.instSortKeySum`, `Engine.modelStore`.

Spec-only, to review: predicates: `Engine.Codec.At`; definitions: `Connection.Fact.opened`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Model.run`, `Engine.eval`, `Engine.instListsModelOfSortKey`, `Engine.instMonadModel`, `Engine.modelStore`. Bridged: none.

#### Community.order_total

Named in the statement: `Community.Crypto`, `Community.Fact`, `Community.InOrder`, `Community.family`, `Community.instSortKeyFact`, `Community.readable`, `Engine.Answer`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Engine.Pos`, `Engine.View.eval`.

Spec-only, to review: predicates: `Community.InOrder`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### PeopleLaws.present_iff

Named in the statement: `Community.Admitted`, `Community.Crypto`, `Community.Fact`, `Community.Key`, `Community.Live`, `Community.family`, `Community.instSortKeyFact`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Engine.View.eval`, `Kinds.Profile.present`.

Spec-only, to review: predicates: `Community.Admitted`, `Community.Live`, `Community.Removed`, `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Community.Fact.admission`, `Community.Fact.removal`, `Engine.specAt`.

Assumed: `Engine.DB`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`).

#### ViewLaws.namesake_iff

Named in the statement: `Community.Crypto`, `Community.Fact`, `Community.Fact.profile`, `Community.V`, `Community.family`, `Community.nameLook`, `Data.Q`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Kinds.Profile.namesake`, `ViewLaws.Model`, `ViewLaws.instReadsModel`, `ViewLaws.nameIn`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; types: `ViewLaws.Model`; definitions: `Community.Fact.profile`, `Engine.specAt`, `ViewLaws.nameIn`; instances: `ViewLaws.instReadsModel`.

Assumed: `Engine.DB`, `Engine.eval`. Bridged: none.

#### Translate.covered

Named in the statement: `Cover.Px`, `Surface.Frame`, `Translate.seen`, `Translate.source`.

Spec-only, to review: definitions: `Translate.position`, `Translate.seen`, `Translate.source`.

Assumed: none. Bridged: none.

#### Cover.line_painted

Named in the statement: `Cover.Px`, `Cover.seen`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Geometry.newest_visible

Named in the statement: `Geometry.Geom`, `Geometry.Geom.Fits`, `Geometry.Geom.composerTop`, `Geometry.Geom.viewNow`, `Geometry.Seam.home`.

Spec-only, to review: predicates: `Geometry.Geom.Fits`; definitions: `Geometry.Seam.home`.

Assumed: none. Bridged: none.

#### Surface.pinned_visible

Named in the statement: `Geometry.Geom`, `Geometry.Geom.composerTop`, `Geometry.Geom.viewNow`, `Surface.Frame.row`, `Surface.make`.

Spec-only, to review: definitions: `Surface.Frame.row`.

Assumed: none. Bridged: none.

#### Geometry.pinned_tap

Named in the statement: `Geometry.Geom`, `Geometry.Geom.Fits`, `Geometry.Seam.tapRow`.

Spec-only, to review: predicates: `Geometry.Geom.Fits`; definitions: `Geometry.Seam.tapRow`.

Assumed: none. Bridged: none.

#### SheetGeom.hit_iff

Named in the statement: `SheetGeom.Grid`, `SheetGeom.Grid.Ok`, `SheetGeom.Grid.hit`, `SheetGeom.Grid.inBox`.

Spec-only, to review: predicates: `SheetGeom.Grid.Ok`, `SheetGeom.Grid.inBox`.

Assumed: none. Bridged: `SheetGeom.Grid.ctop` (by `SheetGeom.lineOf_ctop`).

#### Pages.switcherOrder_complete

Named in the statement: `Pages.Entry`, `Pages.switcherOrder`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Pages.switcherOrder_sound

Named in the statement: `Pages.Entry`, `Pages.switcherOrder`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Text.visual_perm

Named in the statement: `Text.visual`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Image.decode_sized

Named in the statement: `Image.Src`, `Image.decode`, `Pic.maxSide`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Engine.notice_iff

Named in the statement: `Engine.Change`, `Engine.DB`, `Engine.Family`, `Engine.Filing`, `Engine.Inv`, `Engine.OneOpPerId`, `Engine.Pos`, `Engine.SortKey`, `Engine.Subs`, `Engine.Subs.Has`, `Engine.Subs.WF`, `Engine.Subs.notify`, `Engine.Win`, `Engine.runJ`, `Engine.window`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Extends`, `Engine.Inv`, `Engine.OneOpPerId`, `Engine.Spec`, `Engine.Subs.Has`, `Engine.Subs.WF`; types: `Engine.Change`; definitions: `Engine.Change.ingests`, `Engine.specAt`, `Engine.window`.

Assumed: `Engine.DB`, `Engine.matching`, `Engine.runJ`. Bridged: none.

#### Engine.read_notice_iff

Named in the statement: `Engine.Change`, `Engine.DB`, `Engine.Family`, `Engine.Filing`, `Engine.Inv`, `Engine.ListQ`, `Engine.ListQ.win`, `Engine.OneOpPerId`, `Engine.Pos`, `Engine.SortKey`, `Engine.Subs`, `Engine.Subs.Has`, `Engine.Subs.WF`, `Engine.Subs.notify`, `Engine.Win`, `Engine.eval`, `Engine.runJ`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Extends`, `Engine.Inv`, `Engine.OneOpPerId`, `Engine.Spec`, `Engine.Subs.Has`, `Engine.Subs.WF`; types: `Engine.Change`; definitions: `Engine.Change.ingests`, `Engine.specAt`.

Assumed: `Engine.DB`, `Engine.eval`, `Engine.runJ`. Bridged: none.

#### Engine.view_stable

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Id`, `Engine.Inv`, `Engine.Later`, `Engine.SortKey`, `Engine.View`, `Engine.View.eval`, `Engine.View.keys`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Inv`, `Engine.Later`, `Engine.Spec`; definitions: `Engine.View.keys`, `Engine.specAt`.

Assumed: `Engine.DB`, `Engine.eval`. Bridged: `Engine.View.eval` (by `Engine.View.run_model`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.stepS` (by `Engine.run_step`).

#### Engine.eval_stable

Named in the statement: `Engine.Answer`, `Engine.DB`, `Engine.Family`, `Engine.Id`, `Engine.Inv`, `Engine.Later`, `Engine.ListQ`, `Engine.SortKey`, `Engine.eval`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Inv`, `Engine.Later`, `Engine.Spec`; definitions: `Engine.specAt`.

Assumed: `Engine.DB`, `Engine.eval`. Bridged: `Engine.ingestS` (by `Engine.run_ingest`), `Engine.stepS` (by `Engine.run_step`).

#### LiveLaws.read_one_moment

Named in the statement: `Data.Ans`, `Data.Live`, `Data.Live.readWith`, `Data.Q`, `LiveLaws.Agrees`.

Spec-only, to review: predicates: `Engine.Subs.Has`, `Engine.Subs.WF`, `LiveLaws.Agrees`.

Assumed: none. Bridged: none.

#### NodeOffer.offer_split

Named in the statement: `NodeOffer.Chan`, `NodeOffer.offerList`, `NodeOffer.offerM`.

Spec-only, to review: none.

Assumed: `NodeOffer.Chan`, `NodeOffer.offerM`. Bridged: none.

#### Demand.next_visible

Named in the statement: `Demand.next`.

Spec-only, to review: none.

Assumed: none. Bridged: none.

#### Demand.selected_within

Named in the statement: `Demand.SelectionRun`, `Demand.take`.

Spec-only, to review: types: `Demand.SelectionRun`.

Assumed: none. Bridged: none.

#### Engine.window_rows

Named in the statement: `Engine.DB`, `Engine.Family`, `Engine.Inv`, `Engine.ListQ`, `Engine.ListQ.win`, `Engine.Pos`, `Engine.SortKey`, `Engine.eval`, `Engine.window`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; definitions: `Engine.specAt`, `Engine.window`.

Assumed: `Engine.DB`, `Engine.eval`, `Engine.matching`. Bridged: none.

#### Engine.step_costs

Named in the statement: `Engine.CostT`, `Engine.CostT.instMonad`, `Engine.Costs`, `Engine.Family`, `Engine.Family.fileKeys`, `Engine.Id`, `Engine.Op`, `Engine.ReqsLe`, `Engine.Sat`, `Engine.Store`, `Engine.WaitersLe`, `Engine.instStoreCostT`, `Engine.step`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Costs`, `Engine.Field`, `Engine.ReqsLe`, `Engine.Sat`, `Engine.WaitersLe`, `Engine.Within`; instances: `Engine.Meter.instAdd`, `Engine.Meter.instOfNatOfNatNat`.

Assumed: none. Bridged: `Engine.CostT` (the cost meter), `Engine.CostT.bind` (by `Engine.CostT.erase_bind`), `Engine.CostT.charged` (by `Engine.CostT.erase_charged`), `Engine.CostT.chargedBy` (by `Engine.CostT.erase_chargedBy`), `Engine.CostT.instMonad` (the cost meter), `Engine.CostT.pure` (by `Engine.CostT.erase_pure`), `Engine.CostT.run` (by `Engine.CostT.erase_run`), `Engine.instStoreCostT` (the cost meter).

#### Engine.Sync.owed_within

Named in the statement: `Engine.Family`, `Engine.Id`, `Engine.Op`, `Engine.Sync.Config`, `Engine.Sync.Conn`, `Engine.Sync.Conn.serveOwed`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`.

Spec-only, to review: predicates: `Engine.Codec.At`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.lift`, `Engine.modelStore`. Bridged: none.

#### Engine.World.Plain.converge

Named in the statement: `Engine.Id`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.World.Diam`, `Engine.World.Edge`, `Engine.World.Exec`, `Engine.World.Exec.world`, `Engine.World.Holds`, `Engine.World.Net`, `Engine.World.Net.Calm`, `Engine.World.Plain`, `Engine.World.Plain.setup`, `Engine.World.World`.

Spec-only, to review: predicates: `Engine.Codec.At`, `Engine.Sync.Key.lt`, `Engine.World.Diam`, `Engine.World.Edge`, `Engine.World.Holds`, `Engine.World.Legal`, `Engine.World.Net.Calm`, `Engine.World.Net.Live`, `Engine.World.Net.Up`, `Engine.World.Path`; types: `Engine.Sync.Setup`, `Engine.Sync.Who`, `Engine.World.Act`, `Engine.World.Exec`, `Engine.World.Net`, `Engine.World.Packet`, `Engine.World.Plain`, `Engine.World.Setup`, `Engine.World.World`; definitions: `Engine.Sync.Node.connect`, `Engine.Sync.Setup.sync`, `Engine.Sync.plainOpen`, `Engine.Sync.plainSeal`, `Engine.World.Exec.world`, `Engine.World.Plain.setup`, `Engine.World.Plain.two`, `Engine.World.Setup.at?`, `Engine.World.World.enter`, `Engine.World.World.step`, `Engine.World.packets`, `Engine.World.plainPeek`, `Engine.World.upd`, `Engine.World.worlds`.

Assumed: `Engine.DB`, `Engine.DB.addWait`, `Engine.DB.clearWaiters`, `Engine.DB.deleteOp`, `Engine.DB.dependents`, `Engine.DB.index`, `Engine.DB.push`, `Engine.DB.putOp`, `Engine.DB.setStatus`, `Engine.DB.undecide`, `Engine.Model`, `Engine.Model.pop`, `Engine.Sync.Held`, `Engine.Sync.HeldM`, `Engine.Sync.HeldM.run`, `Engine.Sync.instMonadHeldM`, `Engine.Sync.instStoreHeldM`, `Engine.Sync.instTurnHeldM`, `Engine.Sync.lift`, `Engine.budget`, `Engine.modelStore`. Bridged: `Engine.drainS` (by `Engine.run_drain`), `Engine.ingestS` (by `Engine.run_ingest`), `Engine.purgeS` (by `Engine.run_purge`), `Engine.purgeSet` (by `Engine.run_purge`).

#### Heights.anchor_stable

Named in the statement: `Heights.T`, `Heights.screenY`.

Spec-only, to review: types: `Heights.T`; definitions: `Heights.T.size`, `Heights.T.start`, `Heights.T.startM`, `Heights.T.sum`, `Heights.screenY`.

Assumed: none. Bridged: none.

#### Heights.T.find_spec

Named in the statement: `Heights.T`, `Heights.T.WF`, `Heights.T.find`, `Heights.T.start`, `Heights.T.sum`.

Spec-only, to review: predicates: `Heights.T.WF`; types: `Heights.T`; definitions: `Heights.T.find`, `Heights.T.findM`, `Heights.T.size`, `Heights.T.start`, `Heights.T.startM`, `Heights.T.sum`.

Assumed: none. Bridged: none.

#### Heights.rows_cost

Named in the statement: `Engine.CostT.instMonad`, `Engine.CostT.instTick`, `Engine.Counted`, `Engine.Counted.cost`, `Engine.Meter`, `Engine.Meter.instLE`, `Heights.Rows`, `Heights.Rows.Ok`, `Heights.T`, `Heights.T.findM`, `Heights.T.setM`, `Heights.T.startM`.

Spec-only, to review: predicates: `Heights.Rows.Ok`, `Heights.T.Perfect`, `Heights.T.WF`; types: `Heights.Rows`, `Heights.T`; definitions: `Heights.T.findM`, `Heights.T.mk`, `Heights.T.setM`, `Heights.T.size`, `Heights.T.startM`, `Heights.T.sum`, `Heights.T.toList`; instances: `Engine.Meter.instLE`.

Assumed: none. Bridged: `Engine.CostT` (the cost meter), `Engine.CostT.bind` (by `Engine.CostT.erase_bind`), `Engine.CostT.instMonad` (the cost meter), `Engine.CostT.instTick` (the cost meter), `Engine.CostT.pure` (by `Engine.CostT.erase_pure`), `Engine.Counted` (the cost meter), `Engine.Counted.cost` (by `Engine.Counted.cost_run`).

#### Live.World.settle_passes

Named in the statement: `Live.World`, `Live.World.Inv`, `Live.World.frame`, `Live.World.marked`, `Live.World.pass`.

Spec-only, to review: predicates: `Live.Board.Seen`, `Live.World.Inv`; types: `Live.World`; definitions: `Live.Board.apply`, `Live.World.frame`, `Live.World.marked`, `Live.World.pass`.

Assumed: none. Bridged: none.

#### ViewLaws.row_marked

Named in the statement: `Community.Crypto`, `Community.Fact`, `Community.Fact.message`, `Community.Fact.profile`, `Community.V`, `Community.family`, `Community.nameLook`, `Data.Q`, `Engine.DB`, `Engine.Id`, `Engine.Inv`, `Kinds.Message.read`, `Row.RowData`, `ViewLaws.Model`, `ViewLaws.factIn`, `ViewLaws.instReadsModel`, `ViewLaws.nameIn`.

Spec-only, to review: predicates: `Community.V`, `Engine.Codec.At`, `Engine.Inv`, `Engine.Spec`; types: `ViewLaws.Model`; definitions: `Community.Fact.message`, `Community.Fact.profile`, `Engine.specAt`, `Kinds.File.read`, `Kinds.Message.read`, `Kinds.React.read`, `Kinds.React.tally`, `ViewLaws.factIn`, `ViewLaws.nameIn`; instances: `ViewLaws.instReadsModel`.

Assumed: `Engine.DB`, `Engine.eval`. Bridged: none.

#### NodeOffer.offer_runs

Named in the statement: `NodeOffer.run`, `NodeOffer.submitted`.

Spec-only, to review: definitions: `NodeOffer.run`, `NodeOffer.submitted`.

Assumed: `NodeOffer.Chan`, `NodeOffer.offerM`. Bridged: none.

#### Engine.list_costs

Named in the statement: `Engine.Answer`, `Engine.CostT`, `Engine.Costs`, `Engine.Fits`, `Engine.ListQ`, `Engine.Lists`, `Engine.Sat`, `Engine.instListsCostT`.

Spec-only, to review: predicates: `Engine.Costs`, `Engine.Field`, `Engine.Fits`, `Engine.Sat`, `Engine.Within`; definitions: `Engine.countCost`, `Engine.listCost`; instances: `Engine.Meter.instAdd`, `Engine.Meter.instOfNatOfNatNat`.

Assumed: none. Bridged: `Engine.CostT` (the cost meter), `Engine.CostT.chargedBy` (by `Engine.CostT.erase_chargedBy`), `Engine.CostT.run` (by `Engine.CostT.erase_run`), `Engine.instListsCostT` (the cost meter).

#### Engine.Sync.Ingress.Prioritized.write_within

Named in the statement: `Engine.Sync.Ingress.Prioritized.Run`, `Engine.Sync.Ingress.Prioritized.Run.selected`.

Spec-only, to review: types: `Engine.Sync.Ingress.Prioritized.Run`, `Engine.Sync.Ingress.Prioritized.State`; definitions: `Engine.Sync.Ingress.Prioritized.Run.selected`, `Engine.Sync.Ingress.Prioritized.State.arrivals`, `Engine.Sync.Ingress.Prioritized.popEvent`, `Engine.Sync.Ingress.Prioritized.popWrite`, `Engine.Sync.Ingress.Prioritized.step`, `Engine.Sync.Ingress.State.arrivals`.

Assumed: none. Bridged: none.

#### Engine.Sync.Inbox.Priority.write_within

Named in the statement: `Engine.Sync.Inbox.Priority.Run`, `Engine.Sync.Inbox.Priority.Run.selected`.

Spec-only, to review: types: `Engine.Sync.Inbox.Priority.Run`; definitions: `Engine.Sync.Inbox.Priority.Run.selected`, `Engine.Sync.Inbox.Priority.State.append`.

Assumed: none. Bridged: none.
