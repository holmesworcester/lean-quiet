import engine.core.Engine
import engine.core.Merkle
import engine.renderer.Theme

/-
`settings.appearance` (local): this device's appearance, System, Light
or Dark (THEME01). Each one carries a revision, one past the newest this
device holds, and its list sorts by revision, so the preference is the
newest: the list's first row, newest first (`Settings.Appearance.current`,
View.lean). It cites nothing, and is never offered to a peer nor taken
from one: it is local (`Settings.scopeOf`). Before any is written the
preference is System.

This op type's body and fact, their bytes, and the list its fact is
filed in. Its validator is Validate.lean; the registry is
app/settings/Family.lean.
-/

namespace Settings
open Engine Codec

namespace Appearance

/-- A setting's number in an op's bytes. -/
def code : Theme.Setting → Nat
  | .system => 0 | .light => 1 | .dark => 2

/-- The setting a number names; none for any other number. -/
def ofCode : Nat → Option Theme.Setting
  | 0 => some .system | 1 => some .light | 2 => some .dark | _ => none

@[simp] theorem ofCode_code (s : Theme.Setting) : ofCode (code s) = some s := by cases s <;> rfl

/-- What its author writes: the revision and the setting's number. -/
structure Body where
  rev : Nat
  choice : Nat
  deriving BEq

instance : Codec Body := Codec.tagged 40 (fun x => (x.rev, x.choice)) (fun (p : Nat × Nat) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 40 :: Codec.enc (x.rev, x.choice) := rfl

/-- Its fact, `settings.appearance`: the revision and the setting. -/
structure Fact where
  rev : Nat
  setting : Theme.Setting
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 0 (fun x => (x.rev, code x.setting))
  (fun (p : Nat × Nat) => ⟨p.1, (ofCode p.2).getD .system⟩) (fun x => by cases x; simp)

/-- Where it sorts: by revision. -/
def sortKey (f : Fact) : ByteArray := Merkle.be64 f.rev

/-! ## The list its fact is filed in (`settings.appearance.all`) -/
def all : Rel Fact := ⟨"settings.appearance", "all", fun _ => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Appearance

end Settings
