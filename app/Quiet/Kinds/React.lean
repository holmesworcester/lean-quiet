/-
A message's reactions, tallied by emoji: how many people, and whether I
am one.

Reads: `react.byMessage [c, m]` (oldest first: pills keep the order
emoji first arrived). Drawn by Message's view as pills.
-/
import Quiet.Row
import Quiet.Data

namespace Kinds.React
open Engine Community Data

variable {m : Type → Type} [Monad m] [Reads m]

def read (c msg me : Id) (deps : Array Q) : m (List Row.Tally × Array Q) := do
  let (a, _, deps) ← readList (react.byMessage.query [c, msg] (limit := some 500) (desc := false)) deps
  let mut tallies : Array (String × List Id) := #[]
  for (_, f) in a.rows do
    if let .react _ who _ e _ := f then
      let e := (String.fromUTF8? e).getD "?"
      match tallies.findIdx? (·.1 == e) with
      | some i => tallies := tallies.modify i fun (e, us) => (e, if us.contains who then us else us ++ [who])
      | none => tallies := tallies.push (e, [who])
  return (tallies.toList.map fun (e, us) => ⟨e, us.length, us.contains me⟩, deps)

end Kinds.React
