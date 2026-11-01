import app.community.sighting.Op

namespace Community
open Engine Codec

namespace Sighting

/-- It cites the community and its author's admission, whose node key is
the reporter: the reporter's device signs a 32-byte target key and one
valid IPv4 hint. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact
  | ⟨target, addr, time, sig⟩, ⟨c, u0, _, _⟩, ⟨c1, _, d, reporter⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ target.size = 32 ∧
      (Hints.parse addr).isSome ∧ time < 2^64 ∧
      C.verify d (signedBy o (Body.unsigned ⟨target, addr, time, sig⟩)) sig
    then some ⟨c, reporter, target, addr, time⟩ else none

end Sighting

end Community
