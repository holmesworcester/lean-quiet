import ops.community.Op

/-
An admission of a request: a tally. It cites the request and exactly
`threshold` approvals of it, by distinct users. Unsigned: anyone holding
the approvals may compose it. Its fact is the admission (`Root.Fact`).

`community.member.invite.request.approve.admit`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
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
