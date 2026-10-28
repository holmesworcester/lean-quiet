/-
The transient Toast layer. Placement uses the current visible viewport,
not its keyboard-closed height. A card is deferred when it cannot fit
whole; neither its glyphs nor its target is clipped. Time is monotonic
milliseconds (libquiet toast.ts:19–26), independent of render frequency.
`placed_safe`, `placed_view`, `expired` and `dismissed` describe the exact
decisions used by App.withToast.
-/
import Quiet.Occlusion
import Quiet.Paint

namespace Toast
open Safe Occlusion

def life : Nat := 3000

def showing (now : Nat) (pending : Option (String × Nat)) : Option String :=
  pending.bind fun (text, deadline) => if now < deadline then some text else none

def raise (now : Nat) (text : String) : Option (String × Nat) := some (text, now + life)

/-- One whole card, centred in the available Page rectangle. The layer
field is read by `Occlusion.place` before any pixels are copied. -/
def layout (i : Input) (view focused : Rect) (w h : Nat) (key : Nat := 1) : Option Element :=
  let card : Element := ⟨.toast, ⟨view.x + (view.w - w) / 2, view.y + (view.h - h) / 2, w, h⟩⟩
  if card.rect.Inside view ∧ key ≤ w ∧ key ≤ h then
    Occlusion.place i card ⟨.page, view⟩ false focused
  else none

theorem placed_safe (i : Input) (view focused : Rect) (w h key : Nat) (out : Element)
    (ok : layout i view focused w h key = some out) (edge : Edge) :
    out.rect.Disjoint (reserved i edge) ∧ out.rect.Disjoint focused := by
  dsimp only [layout] at ok
  split at ok
  next => exact Occlusion.placed_safe _ _ _ _ _ _ ok edge
  next => contradiction

theorem placed_view (i : Input) (view focused : Rect) (w h key : Nat) (out : Element)
    (ok : layout i view focused w h key = some out) : out.rect.Inside view ∧ out.layer = .toast := by
  dsimp only [layout] at ok
  split at ok
  next hv =>
    unfold Occlusion.place at ok
    split at ok
    next => cases ok; exact ⟨hv.1, rfl⟩
    next => contradiction
  next => contradiction

/-- The whole card is its dismissal target. `key` is the platform minimum
in pixels, supplied by the same density conversion as other controls. -/
theorem placed_size (i : Input) (view focused : Rect) (w h key : Nat) (out : Element)
    (ok : layout i view focused w h key = some out) : key ≤ out.rect.w ∧ key ≤ out.rect.h := by
  dsimp only [layout] at ok
  split at ok
  next hv =>
    unfold Occlusion.place at ok
    split at ok
    next => cases ok; exact hv.2
    next => contradiction
  next => contradiction

theorem expired (now deadline : Nat) (text : String) (h : deadline ≤ now) :
    showing now (some (text, deadline)) = none := by simp [showing, Nat.not_lt.mpr h]

theorem dismissed (now : Nat) : showing now none = none := rfl

theorem raised_visible (now : Nat) (text : String) : showing now (raise now text) = some text := by
  simp [showing, raise, life]

theorem placed_witness :
    layout ⟨1080, 2400, ⟨0, 128, 0, 63⟩, {}, ⟨0, 0, 0, 900⟩⟩
      ⟨0, 350, 1080, 850⟩ ⟨0, 1200, 1080, 300⟩ 735 280 =
      some ⟨.toast, ⟨172, 635, 735, 280⟩⟩ := by decide

end Toast
