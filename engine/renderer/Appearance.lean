/-
You > Appearance, as libquiet's AppearancePage.svelte. The selected
choice has a check and the word Selected, independently of colour.
The page uses the existing Rows painter and tap boxes.
-/
import ops.app.Pages

namespace Appearance

def choices : Array (Theme.Setting × String) :=
  #[(.system, "System"), (.light, "Light"), (.dark, "Dark")]

def label (current choice : Theme.Setting) (name : String) : String :=
  if current == choice then name ++ " · Selected" else name

def page (f : Font.Font) (dm : Row.Dim) (w h : Nat) (current : Theme.Setting) : Pages.Page :=
  let items := choices.map fun (choice, name) =>
    (if current == choice then "✓" else "", label current choice name, Pages.Act.theme choice)
  let (bmp, taps, _) := Pages.rows f dm (Pages.blank w h dm.theme) (dm.px 16) items
  ⟨bmp, taps⟩

def you (f : Font.Font) (dm : Row.Dim) (w h : Nat) : Pages.Page :=
  let (bmp, taps, _) := Pages.rows f dm (Pages.blank w h dm.theme) (dm.px 16)
    #[("◐", "Appearance", Pages.Act.appearance)]
  ⟨bmp, taps⟩

/-- A chosen setting is identified in words, in both palettes. -/
theorem selected_label (s : Theme.Setting) (name : String) :
    label s s name = name ++ " · Selected" := by cases s <;> rfl

end Appearance
