import app.community.member.join.joining.abandon.Op
import app.community.member.join.joining.Op

namespace Community
open Engine Codec

namespace Abandon

/-- Local: it cites the join it stops waiting on. -/
def check (o : Op) : Body → Joining.Fact → Option Fact
  | _, ⟨c, _, _, r, _, _, _⟩ => some ⟨c, r, o.reqs.headD .empty⟩

end Abandon

end Community
