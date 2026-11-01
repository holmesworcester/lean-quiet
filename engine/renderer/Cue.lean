/-
Non-colour state cues: a word or mark for each colour-coded state.
Unread is the word "Unread" (not a count), selected a check, an error
the word "Error", connection a written status. Two are painted today:
the selected check (the row painter, engine/renderer/Row.lean) and the
error's word (the page painter's "Error: …" line, ops/app/Pages.lean);
unread's and connection's cues are not drawn yet. The words do not depend
on a palette; visibility is a layout obligation.
-/
import engine.renderer.Theme

namespace Cue

inductive State where
  | unread | selected | error | connected
  deriving DecidableEq, Repr

def words : State → String
  | .unread => "Unread" | .selected => "✓" | .error => "Error" | .connected => "Connected"

/-- Every colour-coded state has a nonempty non-colour cue. -/
theorem nonempty (s : State) : words s ≠ "" := by cases s <;> decide

def caption (_theme : Theme.Value) (s : State) : String := words s

/-- Theme changes preserve the cue exactly. This holds by definition:
`caption` does not read its theme. It rules out a caption that varies by
theme (tests/app/theme-negative.py's `cue-theme` control), not anything
about how the words are painted. -/
theorem same (a b : Theme.Value) (s : State) : caption a s = caption b s := rfl

end Cue
