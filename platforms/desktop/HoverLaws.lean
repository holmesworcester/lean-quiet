/- Proofs of code called by the desktop shell and component painters. Pixel
agreement with CSS/rasterizers is tested independently; it is not an axiom. -/
import platforms.desktop.Driver
import engine.renderer.HoverLaws

namespace Desktop

theorem pointer_preserves_app (d : Driver) (e : Hover.Event) :
    (pointerEvent d e).app = d.app := rfl

theorem pointer_preserves_tracks (d : Driver) (e : Hover.Event) :
    (pointerEvent d e).layout = d.layout := rfl

theorem pointer_leave_clears (d : Driver) :
    (pointerEvent d .leave).ui.hover = none := rfl

theorem pointer_blur_clears (d : Driver) :
    (pointerEvent d .blur).ui.hover = none := rfl

theorem hover_preserves_row_layout (f : Font.Font) (dm : Row.Dim)
    (w : Nat) (data : Row.RowData) (p : Hover.Context) :
    Row.layout f { dm with hover := p } w data = Row.layout f dm w data := rfl

theorem hover_preserves_composer_layout (f : Font.Font) (dm : Row.Dim)
    (w : Nat) (text : String) (chips : Nat) (wide mobile : Bool) (p : Hover.Context) :
    Composer.layout f { dm with hover := p } w text chips wide mobile =
      Composer.layout f dm w text chips wide mobile := rfl

theorem hover_preserves_sheet_layout (dm : Row.Dim) (w : Nat) (p : Hover.Context) :
    Sheet.quick { dm with hover := p } w = Sheet.quick dm w := rfl

theorem popup_blocks_main (g : Layout) (h : Nat) (ui : Ui)
    (isOpen : ui.switching = true) (inside : Hover.active ui.hover ⟨0, 0, g.width, h⟩ = true) :
    pointer g h ui .main = none := by
  simp [pointer, surfaces, isOpen, Hover.routed, Hover.front, inside, show (Pane.overlay == Pane.main) = false from rfl]

end Desktop
