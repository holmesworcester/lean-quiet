/-
Device appearance. Shells report only the system value; Lean owns the
setting and resolves it. Laws: explicit choices win, System follows the
OS, and the durable spelling round trips. No community or account key.
-/
namespace Theme

inductive Value where
  | light | dark
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Setting where
  | system | light | dark
  deriving BEq, DecidableEq, Repr, Inhabited

structure State where
  setting : Setting := .system
  system : Value := .light
  deriving BEq, Repr, Inhabited

def effective (s : State) : Value :=
  match s.setting with
  | .system => s.system
  | .light => .light
  | .dark => .dark

def encode : Setting → String
  | .system => "system" | .light => "light" | .dark => "dark"

def decode : String → Setting
  | "light" => .light | "dark" => .dark | _ => .system

def ofWord (v : UInt32) : Value := if v == 1 then .dark else .light

/-- System follows the reported OS value. -/
theorem follows (v : Value) : effective ⟨.system, v⟩ = v := rfl

/-- Each explicit choice wins over either OS value. -/
theorem forced (v : Value) :
    effective ⟨.light, v⟩ = .light ∧ effective ⟨.dark, v⟩ = .dark := ⟨rfl, rfl⟩

/-- The setting survives its durable representation. -/
theorem roundtrip (s : Setting) : decode (encode s) = s := by cases s <;> rfl

end Theme
