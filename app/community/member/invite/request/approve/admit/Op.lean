import app.community.Op

/-
An admission of a request: it cites the request and exactly one
approval of it. Unsigned: anyone holding the approval may compose it.
Several admits of one request (citing other approvals) all give the
same admission. Its fact is the admission (`Root.Fact`).
-/

namespace Community
open Engine Codec

namespace Admit

/-- What its author writes. -/
structure Body where
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 11 (fun _ => ()) (fun _ => {}) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = [11] := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact is the root's: an admission. -/
abbrev Fact := Root.Fact

end Admit

end Community
