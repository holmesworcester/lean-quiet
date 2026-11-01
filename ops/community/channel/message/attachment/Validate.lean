import ops.community.channel.message.attachment.Op
import ops.community.channel.message.Op

/-!
`community.channel.message.attachment`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Attach

/-- A child of a message, by its author's user: it cites the community,
its author's admission and the message. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Post.Fact → Option Fact
  | ⟨r, l, k, x, s⟩, ⟨c, u0, _, _⟩, ⟨c1, u, d, _⟩, ⟨c2, u2, _, _, _, _, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ u2 = u ∧ r.size = 32 ∧ 0 < l ∧
      l ≤ maxFile ∧ x.size ≤ maxSealedMeta ∧ C.verify d (signedBy o (Body.unsigned ⟨r, l, k, x, s⟩)) s
    then some ⟨c, o.reqs.getD 2 .empty, u, r, l, k, x⟩ else none

end Attach

end Community
