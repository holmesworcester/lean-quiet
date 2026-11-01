import app.nav.Family

/-
Nav's read: this window's place is the newest nav op's (the first row of
its list, newest first), with that op's id; none before any is written.
The app's page and back stack are this read's cache (`App.St.withNav`).
-/

namespace Nav
open Engine Codec

/-- The newest nav op's id and fact, from the list's first rows. -/
def pick : List (Pos × Fact) → Option (Id × Fact)
  | ((_, x), f) :: _ => some (x, f)
  | [] => none

/-- The list read newest first, one row. -/
def query : ListQ := all.query [] (limit := some 1)

/-- **This window's place**: the newest nav op, with its id. -/
def current : View Fact (Option (Id × Fact)) := do
  let a ← View.read query
  return pick a.rows

end Nav
