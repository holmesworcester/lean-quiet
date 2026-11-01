import app.community.key.wrap.Op

namespace Community
open Engine Codec

namespace Wrap

/-- It cites its community only: a wrap admits nobody. -/
def check (o : Op) : Body → Root.Fact → Option Fact
  | ⟨k, r, bx⟩, ⟨c, u0, _, _⟩ => if o.reqs.head? = some c ∧ u0 = c then some ⟨c, k, r, bx⟩ else none

end Wrap

end Community
