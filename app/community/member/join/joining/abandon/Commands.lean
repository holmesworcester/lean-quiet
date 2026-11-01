import app.community.Family

/-!
`community.member.join.joining.abandon`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine

/-- Whether one of these joins of c by device d is still waited on (not
stopped). -/
def waiting (c : Id) (d : Key) : List (Pos × Fact) → View Fact Bool
  | [] => .pure false
  | ((_, jid), .joining c' _ _ _ _ d' _) :: t =>
    if c' = c ∧ d' = d then
      .list (abandoned.byJoining.query [jid] (limit := some 0)) fun ab =>
        if ab.total = 0 then .pure true else waiting c d t
    else waiting c d t
  | _ :: t => waiting c d t
end Community
namespace Community
open Engine Codec

/-- This device stops waiting on a join (local): its joining op is cited,
the request stays with the members, and an approval still admits it. -/
def abandon (joiningOp : Id) : Op := mkOp [joiningOp] .abandon
end Community
namespace Community
open Engine

/-- Stop waiting on a join: the local record of it is closed. -/
def stopWaiting (joiningOp : Id) : Write := ⟨[abandon joiningOp]⟩

end Community
