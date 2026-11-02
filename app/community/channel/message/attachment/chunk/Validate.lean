import app.community.channel.message.attachment.chunk.Op
import app.community.channel.message.attachment.Op
import engine.core.Merkle

namespace Community
open Engine Codec

namespace Chunk

/-- A chunk is its attachment's: it names the attachment's root, length
and time, and authenticates itself against them. -/
def check (o : Op) : Body → Root.Fact → Attach.Fact → Option Fact
  | ⟨r, l, tm, i, x, p⟩, ⟨c, u0, _, _⟩, ⟨c2, _, _, r2, l2, tm2, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c2 = c ∧ r = r2 ∧ l = l2 ∧ tm = tm2 ∧ Merkle.verify sha256 r l i x p = true
    then some ⟨c, o.reqs.getD 1 .empty, r, l, i⟩ else none

end Chunk

end Community
