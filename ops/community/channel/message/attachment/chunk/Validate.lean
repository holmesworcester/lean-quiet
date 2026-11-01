import ops.community.channel.message.attachment.chunk.Op
import ops.community.channel.message.attachment.Op
import ops.community.Merkle

/-!
`community.channel.message.attachment.chunk`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Chunk

/-- A chunk is its attachment's: it names the attachment's root and
length, and authenticates itself against them. -/
def check (o : Op) : Body → Root.Fact → Attach.Fact → Option Fact
  | ⟨r, l, i, x, p⟩, ⟨c, u0, _, _⟩, ⟨c2, _, _, r2, l2, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c2 = c ∧ r = r2 ∧ l = l2 ∧ Merkle.verify sha256 r l i x p = true
    then some ⟨c, o.reqs.getD 1 .empty, r, l, i⟩ else none

end Chunk

end Community
