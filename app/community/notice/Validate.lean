import app.community.notice.Op

namespace Community
open Engine Codec

namespace Notice

/-- The largest sealed payload: 64 KiB. -/
def maxBox : Nat := 65536

/-- It cites the community and its writer's admission; the writer's
device signs the recipient, the sealed payload and the revision. The
user it is about is the admission's: nobody writes another user's state. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact
  | ⟨r, bx, tm, s⟩, ⟨c, u0, _, _, _⟩, ⟨c1, u, d, _, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ r.size = 32 ∧ bx.size ≤ maxBox ∧
      C.verify d (signedBy o (Body.unsigned ⟨r, bx, tm, s⟩)) s
    then some ⟨c, u, r, bx, tm⟩ else none

end Notice

end Community
