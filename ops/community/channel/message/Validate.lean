import ops.community.channel.message.Op

/-!
`community.channel.message`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Post

/-- It cites the community and its author's admission; a child post also
cites its clump's root, a root post by the same user. The signature
covers the requirements, so receivers do not regroup by time. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact → Option Fact
  | ⟨k, txt, n, tm, s⟩, ⟨c, u0, _, _⟩, ⟨c1, u, d, _⟩, none =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ C.verify d (signedBy o (Body.unsigned ⟨k, txt, n, tm, s⟩)) s
    then some ⟨c, u, d, k, txt, n, tm, none⟩ else none
  | ⟨k, txt, n, tm, s⟩, ⟨c, u0, _, _⟩, ⟨c1, u, d, _⟩, some ⟨c2, u2, _, _, _, _, _, none⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ u2 = u ∧
      C.verify d (signedBy o (Body.unsigned ⟨k, txt, n, tm, s⟩)) s
    then some ⟨c, u, d, k, txt, n, tm, some (o.reqs.getD 2 .empty)⟩ else none
  | _, _, _, some _ => none

end Post

end Community
