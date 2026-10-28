/-
What a node asks its tables when it connects, dials and seals: is this
device a member's, which devices to dial, and which encryption keys a
content key goes to. Each is a view (Engine.View): a composition of
lists, the one read the UI makes too, so the keys a decision watches
are the keys of the lists it read: a device's admissions (key 0), and
the removals of each user they name (key 2); or the community's
admissions (key 1) with the same removals. The laws are in Connect.lean.
-/
import Community.Facts

namespace Community
open Engine

/-- The list of user u's removals in c, counted only. -/
def removals (c u : Id) : ListQ := { key := key 2 c u, limit := some 0 }

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
  let a ← View.read { key := key 0 c d, limit := none }
  let ls ← live c a.rows
  pure (ls.any fun l => decide (l.2.1 = d))

/-- The device keys of c's members: whom to dial. -/
def members (c : Id) : View Fact (List Key) := do
  let a ← View.read { key := key 1 c c, limit := none }
  let ls ← live c a.rows
  pure (ls.map (·.2.1))

/-- The encryption keys a new content key of c is wrapped to. -/
def recipients (c : Id) : View Fact (List Key) := do
  let a ← View.read { key := key 1 c c, limit := none }
  let ls ← live c a.rows
  pure (ls.map (·.2.2))

end Community
