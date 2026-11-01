import app.community.addresses.Op

namespace Community
open Engine Codec

namespace Addresses

/-- It cites the community and its author's admission, whose node key
(`peer`) the hints are for: the author's device signs them, at most
eight valid IPv4 hints, issued before they expire and living at most
`Hints.maxAge`. -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Root.Fact → Option Fact
  | ⟨ds, os, issued, expires, sig⟩, ⟨c, u0, _, _⟩, ⟨c1, _, d, peer⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ Hints.valid (ds ++ os) = true ∧
      issued < expires ∧ expires ≤ issued + Hints.maxAge ∧ expires < 2^64 ∧
      C.verify d (signedBy o (Body.unsigned ⟨ds, os, issued, expires, sig⟩)) sig
    then some ⟨c, peer, ds, os, issued, expires⟩ else none

end Addresses

end Community
