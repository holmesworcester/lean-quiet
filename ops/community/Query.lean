/-
What a node asks its tables when it connects, dials and seals: is this
device a member's, which devices to dial, and which encryption keys a
content key goes to. Each is a view (Engine.View): a composition of
lists, the one read the UI makes too, so the keys a decision watches
are the keys of the lists it read: `admission.byDevice` and the
`removal.byUser` of each user it names; or `admission.all` with the same
removals. `recipients` is what `shareKey` wraps content keys to. The
laws are in Connect.lean.
-/
import ops.community.Facts

namespace Community
open Engine

/-- The list of user u's removals in c, counted only. -/
def removals (c u : Id) : ListQ := removal.byUser.query [c, u] (limit := some 0)

/-- The admissions among these rows into users of c not removed (whose
removals count none): each one's op id, user, device and encryption
key. -/
def live (c : Id) : List (Pos × Fact) → View Fact (List (Id × Id × Key × Key))
  | [] => .pure []
  | ((_, y), .admission c' u d e) :: t =>
    if c' = c then
      .list (removals c u) fun a =>
        (live c t).bind fun rest => .pure (if a.total = 0 then (y, u, d, e) :: rest else rest)
    else live c t
  | _ :: t => live c t

/-- Whether to sync community c with device d: d's admissions, and the
removals of the users they name. -/
def allowPeer (c : Id) (d : Key) : View Fact Bool := do
  let a ← admission.byDevice.read [c, d]
  let ls ← live c a.rows
  pure (ls.any fun l => decide (l.2.2.1 = d))

/-- The device keys of c's members: whom to dial. -/
def members (c : Id) : View Fact (List Key) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map (·.2.2.1))

/-- The live admissions of c, which a content key is wrapped to: each
one's id (what a wrap cites), user and encryption key (`shareKey`). -/
def recipients (c : Id) : View Fact (List (Id × Id × Key)) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (ls.map fun l => (l.1, l.2.1, l.2.2.2))

end Community
