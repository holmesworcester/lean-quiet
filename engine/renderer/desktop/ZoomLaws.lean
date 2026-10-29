/- Laws of zoomLayout, which the desktop Driver actually calls. -/
import engine.renderer.desktop.Laws
import engine.renderer.Font

namespace Desktop

/-- Density 160 is exactly the original CSS layout. -/
theorem zoom_identity (w : Nat) (opened : Bool) : zoomLayout w opened 160 = layout w opened := by
  simp [zoomLayout, layout]

/-- At any density navigation and conversation never overlap. The drawer
is the intentional overlay; it never changes the conversation geometry. -/
theorem zoom_partition (w dpi : Nat) (opened : Bool) :
    (zoomLayout w opened dpi).nav.x + (zoomLayout w opened dpi).nav.w ≤
      (zoomLayout w opened dpi).main.x ∧
    (zoomLayout w opened dpi).main.x + (zoomLayout w opened dpi).main.w ≤ w := by
  have hp : (220 * dpi + 80) / 160 ≤ (720 * dpi + 80) / 160 := by
    exact Nat.div_le_div_right (by omega)
  by_cases hw : (720 * dpi + 80) / 160 ≤ w <;> cases opened <;> simp [zoomLayout, hw] <;> omega

/-- Every track is contained even at fractional zoom levels. -/
theorem zoom_contained (w dpi : Nat) (opened : Bool) (p : Pane) :
    ((zoomLayout w opened dpi).track p).x + ((zoomLayout w opened dpi).track p).w ≤ w := by
  have hp : (375 * dpi + 80) / 160 ≤ (720 * dpi + 80) / 160 :=
    Nat.div_le_div_right (by omega)
  have hn : (220 * dpi + 80) / 160 ≤ (720 * dpi + 80) / 160 :=
    Nat.div_le_div_right (by omega)
  by_cases hw : (720 * dpi + 80) / 160 ≤ w <;> cases opened <;> cases p <;> simp [zoomLayout, hw, Layout.track] <;> omega

/-- Zoomed controls use the same containment filter as their hit tests. -/
theorem zoom_controls_screen (w h dpi : Nat) (opened : Bool)
    (xs : List (Control α)) (c : Control α) (minimum : Nat)
    (hc : c ∈ controls (zoomLayout w opened dpi) h xs minimum) :
    c.box.x + c.box.w ≤ w ∧ c.box.y + c.box.h ≤ h := by
  have hf : Fits (zoomLayout w opened dpi) h c.pane c.box minimum := by
    simpa [controls] using (List.mem_filter.mp hc).2
  have ht := zoom_contained w dpi opened c.pane
  exact ⟨Nat.le_trans hf.2.1 ht, hf.2.2.1⟩

/-- Opening the drawer never reflows the conversation on a wide viewport. -/
theorem zoom_drawer_preserves (w dpi : Nat) (hw : (720 * dpi + 80) / 160 ≤ w) :
    (zoomLayout w true dpi).main = (zoomLayout w false dpi).main := by
  simp [zoomLayout, hw]
/-- Raising density cannot shrink the body's cell. This is the actual
font-size selector used by Font.load, including its rasterizer limits. -/
theorem zoom_font_monotone (source a b : Nat) (h : a ≤ b) :
    Font.pixelCell source a ≤ Font.pixelCell source b := by
  unfold Font.pixelCell
  have hd : (14 * a + 80) / 160 ≤ (14 * b + 80) / 160 := Nat.div_le_div_right (by omega)
  omega

end Desktop
