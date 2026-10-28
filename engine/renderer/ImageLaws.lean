/-
The app's picture decode is the proven one: `Image.decode` is
`Pic.decode` (Pic/Laws' hostile-input laws are about it), its pixels
made words, so what Pic.decode_sized says holds of what the app draws.
-/
import engine.renderer.Image
import engine.renderer.pic.Laws

namespace Image

/-- **Whatever the bytes, a picture the app decodes has sides of 1 to
2048 and exactly their pixels** (Pic.decode_sized, carried through). -/
theorem decode_sized {b : ByteArray} {s : Src} (h : decode b = some s) :
    1 ≤ s.w ∧ s.w ≤ Pic.maxSide ∧ 1 ≤ s.h ∧ s.h ≤ Pic.maxSide ∧ s.px.size = s.w * s.h := by
  unfold decode at h
  cases hp : Pic.decode b with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3, h4, -⟩ := Pic.decode_sized hp
    exact ⟨h1, h2, h3, h4, by simp [Src.ofRgba]⟩

end Image
