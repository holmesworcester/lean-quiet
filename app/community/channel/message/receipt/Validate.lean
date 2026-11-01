import app.community.channel.message.receipt.Op
import app.community.channel.message.Op

/-!
`community.channel.message.receipt`'s validator: the fact it produces from the facts it
cites. The engine calls it only once every one of them is Valid.
-/

namespace Community
open Engine Codec

namespace Receive

/-- This device's receipt of a saturated post: local, so it may read what
it cites, and its counter is the writer's (`receiptFor`). -/
def check (o : Op) : Body → Post.Fact → Option Fact
  | ⟨k⟩, ⟨c, _, _, kid, _, n, _, clump⟩ =>
    if countCap ≤ n then some ⟨c, kid, o.reqs.headD .empty, k, clump⟩ else none

end Receive

end Community
