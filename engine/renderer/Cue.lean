/-
Non-colour state cues, used by the row and page painters. Unread has a
count, selected a check, errors words, and connection a written status.
The words do not depend on a palette; visibility is a layout obligation.
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

/-- Theme changes preserve the cue exactly. -/
theorem same (a b : Theme.Value) (s : State) : caption a s = caption b s := rfl

end Cue
