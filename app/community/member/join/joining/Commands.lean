import engine.wire.Node
import app.community.Family

/-!
`community.member.join.joining`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- This device's pending join (local): the link's community, its
inviter and hints, the request the join presents, and the name to
introduce itself by once admitted. The bearer seed is not kept: the
request already carries the bearer's signature. -/
def joining (i : Invite) (req : Id) (name : ByteArray) (device : Key) (epoch : Nat := 0) : Op :=
  mkOp [] (.joining i.community i.inviter i.hints req name device epoch)
end Community
namespace Community
open Engine

/-- The latest join of c among these whose device was never admitted in
c: one stopped waiting on, to resume. -/
def dormant (c : Id) : List (Pos × Fact) →
    View Fact (Option (Key × List ByteArray × Id × ByteArray × Key × Nat))
  | [] => .pure none
  | (_, .joining c' k hs r nm d n) :: t =>
    if c' = c then
      .list (admission.byDevice.query [c, d] (limit := some 0)) fun a =>
        (dormant c t).bind fun rest => .pure (
          if a.total ≠ 0 then rest else
          match rest with
          | some (_, _, _, _, _, m) => if n ≥ m then some (k, hs, r, nm, d, n) else rest
          | none => some (k, hs, r, nm, d, n))
    else dormant c t
  | _ :: t => dormant c t

end Community
