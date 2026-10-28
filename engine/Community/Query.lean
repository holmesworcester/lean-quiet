/-
What a node asks its tables when it connects, dials and seals: is this
device a member's, which devices to dial, and which encryption keys a
content key goes to. Each is a view (Engine.View): a composition of
lists, the one read the UI makes too, so the keys a decision watches
are the keys of the lists it read: `admission.byDevice` and the
`removal.byUser` of each user it names; or `admission.all` with the same
removals. The laws are in Connect.lean.
-/
import Community.Facts

namespace Community
open Engine

/-- The list of user u's removals in c, counted only. -/
def removals (c u : Id) : ListQ := removal.byUser.query [c, u] (limit := some 0)

/-- The admissions among these rows into users of c not removed (whose
removals count none): each one's user, device and encryption key. -/
def live (c : Id) : List (Pos × Fact) → View Fact (List (Id × Key × Key))
  | [] => .pure []
  | (_, .admission c' u d e) :: t =>
    if c' = c then
      .list (removals c u) fun a =>
        (live c t).bind fun rest => .pure (if a.total = 0 then (u, d, e) :: rest else rest)
    else live c t
  | _ :: t => live c t

/-- Whether to sync community c with device d: d's admissions, and the
removals of the users they name. -/
def allowPeer (c : Id) (d : Key) : View Fact Bool := do
  let a ← admission.byDevice.read [c, d]
  let ls ← live c a.rows
  pure (ls.any fun l => decide (l.2.1 = d))

/-- The device keys of c's members: whom to dial. -/
def members (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map (·.2.1))

/-- The encryption keys a new content key of c is wrapped to. -/
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

/-- Whether device d is live in c: admitted, and none of the users it is
admitted into removed. Removing any user of a device cuts it, wherever
else it is admitted (docs/REMOVAL.md, "One device, two users"). -/
def deviceLive (c : Id) (d : Key) : View Fact Bool := do
  let a ← admission.byDevice.read [c, d]
  let xs ← removalsOf c a.rows
  pure (!a.rows.isEmpty && xs.isEmpty)

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
  let xs ← deviceRemovals c a.rows
  pure xs.eraseDups

end Community
