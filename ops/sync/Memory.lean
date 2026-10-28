/-
Bounded sync hints. Remembering a new peer id may forget old hints;
admission reserves only free ask slots. Neither operation ends a session.
The laws of these helpers and their callers are in BoundsLaws.
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

/-- Only fresh, distinct ids that fit are admitted, in offer order. -/
def admitAsks (cap : Nat) (asked : HashSet Id) (ids : List Id) : List Id :=
  ((ids.filter fun i => !asked.contains i).eraseDups).take (cap - asked.size)

end Engine.Sync
