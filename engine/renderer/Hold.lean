/- Shared placeholder pixels for App.listFrame and the compositor.
The legacy 48-pixel tile remains for old compositor fixtures/contracts.
App uses the density-scaled message silhouette and publishes its period. -/
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

/-- Message geometry, in the same dp and columns as painted Row components. -/
def period (d : Row.Dim) : Nat := max 1 (d.px 80)

private def capsule (row : ByteArray) (W x y w h radius line : Nat) (c : Color) : ByteArray := Id.run do
  if line < y || line ≥ y + h then return row
  let mut row := row
  let right := min W (x + w)
  let radius := min radius (min (w / 2) (h / 2))
  for px in [min x W:right] do
    let coverage := Paint.cover x y (x + w) (y + h) radius px line
    if coverage > 0 then row := Paint.setPx row px (Paint.mixC (Paint.getPx row px) c coverage)
  return row

/-- Quiet, static message skeleton: avatar, author/time and two text lines.
It deliberately contains no animation, query state or platform assumptions. -/
def messageLine (s : St) (li : Nat) : ByteArray := Id.run do
  let d := s.dim
  let y := li % period d
  let ink := Palette.color d.theme .line
  let header := Paint.blendText (Palette.color d.theme .muted) (Palette.color d.theme .bg) 64
  let available := s.W - d.textX - d.pad
  let body := min available (d.px 360)
  let name := min available (d.px 88)
  let mut row := capsule s.bgRow s.W d.pad (d.px 8) d.avatar d.avatar (d.px 6) y ink
  row := capsule row s.W d.textX (d.px 10) name (max 1 (d.px 10)) (d.px 3) y header
  let timeX := d.textX + name + d.px 8
  row := capsule row s.W timeX (d.px 12) (min (s.W - timeX - d.pad) (d.px 32))
    (max 1 (d.px 6)) (d.px 3) y ink
  row := capsule row s.W d.textX (d.px 30) body (max 1 (d.px 10)) (d.px 3) y ink
  row := capsule row s.W d.textX (d.px 48) (body * 2 / 3) (max 1 (d.px 10)) (d.px 3) y ink
  return row

/-- Unloaded distances count upwards; message silhouettes read top-down. -/
def unloadedLine (s : St) (content : Nat) : ByteArray :=
  messageLine s (period s.dim - 1 - content % period s.dim)

/-- The native fill plane and pending component rows use identical pixels. -/
def messagePlane (s : St) (height : Nat) : Array ByteArray :=
  let n := period s.dim
  let tile := (Array.range n).map fun i => messageLine s i
  (Array.range (height + n)).map fun i => tile[i % n]!
end Hold
