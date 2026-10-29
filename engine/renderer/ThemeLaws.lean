/-
Theme laws over the running app's transition and the renderer's colour
resolver. Layout ownership and later occlusion are separate obligations:
text must still be visible, and copied layers must keep their pixels.
-/
import App
import engine.renderer.Cue

namespace ThemeLaws
open App Paint

/-- No row, image, sheet cell, page or chrome from the old theme remains
reachable after the transition, including their asynchronous tasks. -/
theorem cleared (s : St) (t : Theme.State) :
    (themed s t).rows = {} ∧ (themed s t).imgs = {} ∧
    (themed s t).gridRows = {} ∧ (themed s t).pageNow = none ∧
    (themed s t).pageKey = none ∧ (themed s t).chromeKey = "" ∧
    (themed s t).topBmp.rows = #[] ∧ (themed s t).botBmp.rows = #[] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The new background and every painter's palette input agree with the
new effective theme, regardless of the previous cache contents. -/
theorem palette (s : St) (t : Theme.State) :
    (themed s t).dim.theme = Theme.effective t ∧
    (themed s t).bgRow = solid (Palette.color (Theme.effective t) .bg) s.W := ⟨rfl, rfl⟩

/-- Theme changes preserve the content and layout inputs. -/
theorem content (s : St) (t : Theme.State) :
    (themed s t).me = s.me ∧ (themed s t).ids = s.ids ∧
    (themed s t).text = s.text ∧ (themed s t).W = s.W ∧
    (themed s t).dim.dpi = s.dim.dpi ∧ (themed s t).dim.cell = s.dim.cell :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The glyph painter's actual colour selector meets 4.5:1 against the
composited pixel below, for every possible RGB background. -/
theorem text (wanted : Color) (row : ByteArray) (x : Nat) :
    Contrast.meets (textColor wanted row x) (getPx row x) := Contrast.ink_meets _ _

end ThemeLaws
