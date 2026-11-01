import ops.community.Family

/-!
`community.member.invite.request.approve`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- by_'s approval of request req, signed as its admission adm. -/
def approve (c req adm : Id) (by_ : Device) : Op :=
  let reqs := [c, req, adm]
  mkOp reqs (.approve (sig by_.sk reqs (.approve .empty)))

end Community
