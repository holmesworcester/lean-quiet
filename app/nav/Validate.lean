import app.nav.Op

namespace Nav
open Engine Codec

/-- It cites nothing: any place is a place. -/
def check (o : Op) : Body → Option Fact
  | ⟨gen, page, stack⟩ => if o.reqs = [] then some ⟨gen, page, stack⟩ else none

end Nav
