import app.settings.Family

/-
Appearance's intent (THEME01): choosing a setting writes one op, a
revision past the newest this device holds. An honest choice is Valid
(`choose_valid`) and local.
-/

namespace Settings
open Engine Codec

namespace Appearance

/-- The op choosing s, at revision rev. -/
def choose (rev : Nat) (s : Theme.Setting) : Op := mkOp [] (Settings.Body.ofAppearance ⟨rev, code s⟩)

/-- **An honest choice is Valid,** with the setting chosen. -/
theorem choose_valid (rev : Nat) (s : Theme.Setting) :
    Settings.validate (choose rev s) [] = some (Settings.Fact.ofAppearance ⟨rev, s⟩) := by
  simp [Settings.validate, choose, mkOp, Codec.decode_encode, Settings.Body.kind, Settings.check, Appearance.check]


end Appearance

end Settings
