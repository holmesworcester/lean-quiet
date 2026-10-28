/-
Bounded sync hints. Remembering a new peer id may forget old hints; an
ask past the cap is sent all the same, only not remembered (never
deferred). Neither ends a session. The laws of these helpers and their
callers are in BoundsLaws.
-/
import engine.core.Core
import Std.Data.HashSet
import Std.Data.HashMap

namespace Engine.Sync
open Std

/-- Forget hints before an insertion would exceed the cap; zero disables them. -/
def remember (cap : Nat) (known : HashSet Id) (i : Id) : HashSet Id :=
  if cap = 0 then {} else
  let next := known.insert i
  if next.size ≤ cap then next else ({} : HashSet Id).insert i

/-- The ids to ask for: not asked in this period or the last, distinct,
in offer order. Every one is wanted (`noteAsks` remembers what fits). -/
def freshAsks (asked stale : HashSet Id) (ids : List Id) : List Id :=
  (ids.filter fun i => !asked.contains i && !stale.contains i).eraseDups

/-- Remember asks while there is room for them. -/
def noteAsks (cap : Nat) (asked : HashSet Id) (ids : List Id) : HashSet Id :=
  ids.foldl (fun s i => if s.size < cap then s.insert i else s) asked

end Engine.Sync
