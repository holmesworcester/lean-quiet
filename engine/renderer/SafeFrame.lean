/-
The inset report and the frame's Chrome edges. Layout works at content
width; `extend` adds only the left and right reserved pixels to the same
three frames the seam already places. It does not place or classify taps.
Colours are today's tokens, behind `edgeColour`; the theme branch can
supply `Colours` from its palette without changing inset geometry.
-/
import engine.renderer.Safe
import ops.app.Pages
import engine.renderer.Sheet

namespace SafeFrame
open Safe Paint

/-- The existing six-word report followed by side bars, keyboard height,
and the cutout's left/top/right/bottom. Legacy twins may omit the suffix. -/
def report (sc : Array UInt32) (ime : Nat := 0) : Input :=
  let n (k : Nat) (fallback := 0) := (sc[k]?.getD fallback.toUInt32).toNat
  ⟨n 0 1080, n 1 2400, ⟨n 6, n 2, n 7, n 3⟩,
    ⟨n 9, n 10, n 11, n 12⟩, ⟨0, 0, 0, n 8 ime⟩⟩

inductive Screen where
  | page | home | channel | sheet
  deriving BEq, DecidableEq, Repr, Inhabited

structure Colours where
  page : Color
  home : Color
  channel : Color
  sheet : Color

def colours (theme : Theme.Value) : Colours :=
  ⟨Palette.color theme .bg, Palette.color theme .panel, Palette.color theme .panel, Palette.color theme .panel⟩

def current : Colours := colours .dark

/-- Round a minimum up: rounding to nearest could make 48 dp smaller. -/
def targetPx (dpi : Nat) : Nat := (48 * dpi + 159) / 160

theorem target_minimum (dpi : Nat) : 48 * dpi ≤ 160 * targetPx dpi := by
  unfold targetPx
  omega

/-- The one edge policy. The supplied palette is the screen's theme. -/
def edgeColour (screen : Screen) (theme : Colours) (edge : Edge) : Color :=
  match screen, edge with
  | .home, .top => theme.home
  | .channel, .top | .sheet, .top => theme.channel
  | .sheet, .bottom => theme.sheet
  | _, _ => theme.page

/-- Choose the higher-contrast black or white system glyphs from the
actual edge colour. sRGB/WCAG luminance; Float evaluation is tested, not
a contrast proof. The palette branch owns composited contrast laws. -/
def lightIcons (c : Color) : Bool :=
  let linear (v : UInt8) :=
    let s := v.toNat.toFloat / 255
    if s ≤ 0.04045 then s / 12.92 else Float.pow ((s + 0.055) / 1.055) 2.4
  let l := 0.2126 * linear (r8 c) + 0.7152 * linear (g8 c) + 0.0722 * linear (b8 c)
  1.05 / (l + 0.05) ≥ (l + 0.05) / 0.05

structure Band where
  rect : Rect
  colour : Color

def band (i : Input) (screen : Screen) (theme : Colours) (edge : Edge) : Band :=
  ⟨reserved i edge, edgeColour screen theme edge⟩

theorem band_colour (i : Input) (screen : Screen) (theme : Colours) (edge : Edge) :
    (band i screen theme edge).colour = edgeColour screen theme edge := rfl

/-- A whole row with side fills. Input rows remain shared when there are
no side insets. Both fills take their adjacent pixel's colour, including
the header and sheet segments of a landscape edge. -/
def extend (i : Input) (rows : Array ByteArray) : Array ByteArray := Id.run do
  let r := content { i with ime := {} }
  if r.x == 0 && r.w == i.w then return rows
  return rows.map fun row =>
    let left := solid (getPx row 0) r.x
    let right := solid (getPx row (r.w - 1)) (i.w - r.right)
    left ++ row ++ right

end SafeFrame
