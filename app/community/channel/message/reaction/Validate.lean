import app.community.channel.message.reaction.Op
import app.community.channel.message.Op

namespace Community
open Engine Codec

namespace React

/-- It cites the community, its author's admission and the message. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Post.Fact → Option Fact
  | ⟨e, tm, s⟩, ⟨c, u0, _, _, _⟩, ⟨c1, u, d, _, _⟩, ⟨c2, _, _, _, _, _, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ 0 < e.size ∧ e.size ≤ 32 ∧
      C.verify d (signedBy o (Body.unsigned ⟨e, tm, s⟩)) s
    then some ⟨c, u, o.reqs.getD 2 .empty, e, tm⟩ else none

end React

end Community
