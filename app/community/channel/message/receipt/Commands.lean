import app.community.Family

namespace Community
open Engine

/-- The counter of this device's newest receipt in c (0 for none). -/
def topReceived (c : Id) : View Fact Nat := do
  let a ← received.all.read [c] (limit := some 1)
  pure (match a.rows.head? with
    | some (_, .received _ _ _ k _) => k
    | _ => 0)
open Engine Codec

/-- This device's k-th receipt of saturated message m (local). -/
def receipt (m : Id) (k : Nat) : Op := mkOp [m] (.receive k)
open Engine

/-- What this device writes on receiving op o, sent from here or
arrived: for a post claiming the counter cap or more, its receipt, one
past this device's newest receipt in the post's community, unless it
holds one of o already. Nothing for any other op, whose body it does
not decode (a post is kind 23). The network node writes it on every
arrival (`Connection.onArrival`); `send` with the post. -/
def receiptFor (o : Op) : View Fact (List Op) := do
  if o.kind ≠ 23 then return []
  match (Codec.decode o.body : Option Body) with
  | some (.post _ _ n _ _) =>
    if n < countCap then return []
    let held ← received.byMsg.read [o.id] (limit := some 0)
    if held.total ≠ 0 then return []
    return [receipt o.id ((← topReceived (o.reqs.headD .empty)) + 1)]
  | _ => return []

/-- A row of `received.byKey` as its message's: the message's id, at
the receipt's position. -/
def asMsg (r : Pos × Fact) : Pos × Fact :=
  match r.2 with
  | .received _ _ m _ _ => ((r.1.1, m), r.2)
  | _ => r

end Community
