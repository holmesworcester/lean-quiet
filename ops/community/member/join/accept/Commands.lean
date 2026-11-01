import ops.community.Family

/-!
`community.member.join.accept`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- This device is in community c (local). -/
def accept (c : Id) (device : Key) : Op := mkOp [] (.accept c device)

end Community
