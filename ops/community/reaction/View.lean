/-
A message's reactions, tallied by emoji: how many people, and whether I
am one.

Reads: `react.byMessage [c, m]` (oldest first: pills keep the order
emoji first arrived). Drawn by Message's view as pills.
-/
import engine.renderer.Row
import engine.renderer.Data

namespace Kinds.React
open Engine Community Data

/-- A list's distinct elements, each at its first place. -/
def uniq {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: t => x :: uniq (t.filter fun y => !decide (y = x))
termination_by l => l.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp)))

/-- Reactions (emoji, reactor) into tallies: each emoji once, in the order
it first arrived, with the distinct people who reacted with it. Laws
(RowLaws): `tally_nodup`, `tally_mem`. -/
def tally (xs : List (String × Id)) : List (String × List Id) :=
  (uniq (xs.map (·.1))).map fun e => (e, uniq ((xs.filter fun p => decide (p.1 = e)).map (·.2)))

variable {m : Type → Type} [Monad m] [Reads m]

def read (c msg me : Id) (deps : Array Q) : m (List Row.Tally × Array Q) := do
  let (a, _, deps) ← readList (react.byMessage.query [c, msg] (limit := some 500) (desc := false)) deps
  let xs := a.rows.filterMap fun (_, f) => match f with
    | .react _ who _ e _ => some ((String.fromUTF8? e).getD "?", who)
    | _ => none
  return ((tally xs).map fun (e, us) => ⟨e, us.length, us.any (fun x => decide (x = me))⟩, deps)

end Kinds.React
