import app.community.channel.message.attachment.Op
import app.community.channel.message.Op

namespace Community
open Engine Codec

namespace Attach

/-- A child of a message, by its author's user: it cites the community,
its author's admission and the message, and claims the message's time. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Post.Fact → Option Fact
  | ⟨r, l, tm, k, x, s⟩, ⟨c, u0, _, _⟩, ⟨c1, u, d, _⟩, ⟨c2, u2, _, _, _, _, tm2, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ u2 = u ∧ tm = tm2 ∧ r.size = 32 ∧ 0 < l ∧
      l ≤ maxFile ∧ x.size ≤ maxSealedMeta ∧ C.verify d (signedBy o (Body.unsigned ⟨r, l, tm, k, x, s⟩)) s
    then some ⟨c, o.reqs.getD 2 .empty, u, r, l, tm, k, x⟩ else none

end Attach

end Community
