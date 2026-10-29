/- Shared placeholder pixels for App.listFrame and the compositor.
The body of main's App.holdLine is unchanged; St projects its three inputs.
Translate.hold_row and fill_pixel connect the published plane to this line. -/
import engine.renderer.Row
namespace Hold
open Paint
structure St where
  bgRow : ByteArray
  dim : Row.Dim
  W : Nat
def holdLine (s : St) (li : Nat) : ByteArray :=
  if li % 48 < 12 || li % 48 ≥ 36 then s.bgRow
  else
    let x0 := s.dim.pad + s.dim.px 48
    let w := max 1 (s.W * 2 / 3 - x0)
    (solid (Palette.color s.dim.theme .selected) w).copySlice 0 s.bgRow (4 * x0) (4 * w)

/-- One period, reversed because content distances count upwards. -/
def tile (s : St) : Array ByteArray := (Array.range 48).map fun i => holdLine s (47 - i)

/-- Shared rows, expanded once per Lean frame for a compositor fill plane. -/
def plane (s : St) (height : Nat) : Array ByteArray :=
  let t := tile s
  (Array.range (height + 48)).map fun i => t[i % 48]!
end Hold
