import app.community.Family

namespace Community
open Engine

/-- This device's mark in c: it has taken notice of posts claiming
times up to `mark` (local). -/
def caughtUp (c : Id) (mark : Nat) : Op := mkOp [] (.caughtUp c mark)

/-- This device's newest mark in c, if it has one. -/
def markOf (c : Id) : View Fact (Option Nat) := do
  let a ← caughtUp.byCommunity.read [c] (limit := some 1)
  pure (match a.rows.head? with
    | some (_, .caughtUp _ m) => some m
    | _ => none)

end Community
