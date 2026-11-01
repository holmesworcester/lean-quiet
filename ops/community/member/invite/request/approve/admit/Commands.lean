import ops.community.Family

/-!
`community.member.invite.request.approve.admit`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- The admission of request req by these approvals. -/
def admit (c req : Id) (approvals : List Id := []) : Op := mkOp (c :: req :: approvals) .admit

end Community
