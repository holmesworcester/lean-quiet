import app.connection.request.Op

namespace Connection
open Engine Codec

namespace Request

/-- It cites nothing: it travels bare, to one peer. -/
def check : Body → Option Fact
  | ⟨to, frm, m1⟩ =>
    if to.size = 32 ∧ frm.size = 32 ∧ to ≠ frm ∧ 48 ≤ m1.size
    then some ⟨to, frm, m1⟩ else none

end Request

end Connection
