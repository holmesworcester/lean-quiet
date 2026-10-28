/-
What a node asks its tables when it connects, dials and seals: which
node keys to let in, which devices to dial, and which keys a content key
goes to. Each is a view (Engine.View): a composition of lists, the one
read the UI makes too, so the keys a decision watches are the keys of
the lists it read. The laws are in Connect.lean and RemovalLaws.lean.

A device counts while it is live: admitted, and none of the users it is
admitted into removed (`deviceLive`: its `admission.byDevice` rows and
each one's user's `removal.byUser`). Removing any of its users cuts it,
wherever else it is admitted (docs/REMOVAL.md, "One device, two
users"). A node key is let in while a device admitted under it is live
(`allowPeer`: `admission.byKey`, then each device's liveness).
-/
import ops.community.Facts

namespace Community
open Engine

/-- The list of user u's removals in c, counted only. -/
def removals (c u : Id) : ListQ := removal.byUser.query [c, u] (limit := some 0)

/-- Whether every admission into c among these rows is into a user with
no removal. -/
def unremoved (c : Id) : List (Pos × Fact) → View Fact Bool
  | [] => .pure true
  | (_, .admission c' u _ _) :: t =>
    if c' = c then
      .list (removals c u) fun a => if a.total = 0 then unremoved c t else .pure false
    else unremoved c t
  | _ :: t => unremoved c t

/-- Whether device d is live in c: admitted, and none of the users it is
admitted into removed. -/
def deviceLive (c : Id) (d : Key) : View Fact Bool := do
  let a ← admission.byDevice.read [c, d]
  if a.rows.isEmpty then pure false else unremoved c a.rows

/-- The admissions into c among these rows whose device is live: each
one's user, device and key. -/
def live (c : Id) : List (Pos × Fact) → View Fact (List (Id × Key × Key))
  | [] => .pure []
  | (_, .admission c' u d e) :: t =>
    if c' = c then
      (deviceLive c d).bind fun ok =>
        (live c t).bind fun rest => .pure (if ok then (u, d, e) :: rest else rest)
    else live c t
  | _ :: t => live c t

/-- Whether to sync community c with the node whose key is e: the
admissions under e, and whether each one's device is live. -/
def allowPeer (c : Id) (e : Key) : View Fact Bool := do
  let a ← admission.byKey.read [c, e]
  let ls ← live c a.rows
  pure (ls.any fun l => decide (l.2.2 = e))

/-- The device keys of c's live devices. -/
def members (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map (·.2.1))

/-- The node keys a new content key of c is wrapped to: those with a
live device, the keys `allowPeer` lets in. -/
def recipients (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map (·.2.2))

/-- This node's key: its endpoint op's public key and secret (the least
id, should it ever hold two). -/
def nodeKey : View Fact (Option (Key × ByteArray)) := do
  let a ← endpoint.all.read [] (limit := some 1)
  pure (a.rows.head?.bind fun (_, f) => match f with
    | .endpoint pk sk => some (pk, sk)
    | _ => none)

/-- Of these rows, each admission's user's removals in c, as op ids. -/
def removalsOf (c : Id) : List (Pos × Fact) → View Fact (List Id)
  | [] => .pure []
  | (_, .admission _ u _ _) :: t =>
    .list (removal.byUser.query [c, u]) fun a =>
      (removalsOf c t).bind fun rest => .pure (a.rows.map (·.1.2) ++ rest)
  | _ :: t => removalsOf c t

/-- Of these admission rows, the removals of every user each row's
device is admitted into, under any key. -/
def deviceRemovals (c : Id) : List (Pos × Fact) → View Fact (List Id)
  | [] => .pure []
  | (_, .admission _ _ d _) :: t =>
    .list (admission.byDevice.query [c, d]) fun a =>
      (removalsOf c a.rows).bind fun xs =>
        (deviceRemovals c t).bind fun rest => .pure (xs ++ rest)
  | _ :: t => deviceRemovals c t

/-- The removals that cut the devices admitted under key e in c: every
removal of a user any of those devices is admitted into. What a node
holding them owes the node at e once none of its devices is live, so
that node can judge itself cut (docs/REMOVAL.md). -/
def removalsAt (c e : Key) : View Fact (List Id) := do
  let a ← admission.byKey.read [c, e]
  deviceRemovals c a.rows

end Community
