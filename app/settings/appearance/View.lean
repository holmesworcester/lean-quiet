import app.settings.Family

/-
Appearance's read: the preference is the newest appearance's setting (the
first row of its list, newest first), with its revision; System at
revision 0 before any is written (THEME01). The shell reads it at launch
and after each choice.
-/

namespace Settings
open Engine Codec

namespace Appearance

/-- The preference and its revision, from the list's first rows. -/
def pick : List (Pos × Settings.Fact) → Theme.Setting × Nat
  | (_, .ofAppearance f) :: _ => (f.setting, f.rev)
  | [] => (.system, 0)

/-- The list read newest first, one row. -/
def query : ListQ := appearance.all.query [] (limit := some 1)

/-- **The preference**: the newest appearance's setting and revision. -/
def current : View Settings.Fact (Theme.Setting × Nat) := do
  let a ← View.read query
  return pick a.rows

/-- Before any appearance is written, the preference is System. -/
theorem pick_nil : pick [] = (.system, 0) := rfl

end Appearance

end Settings
