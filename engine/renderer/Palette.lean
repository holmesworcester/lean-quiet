/-
The app's colour source. libquiet ab3d244c, design/tokens.css and
design/theme.css: explicit light/dark token sets, never an inversion.
Page, Chrome, Marks, Surface and Toast use these roles. Meaningful
edges use ink rather than the decorative --line. Contrast certifies
composited ink separately, including colours behind an overlay.
-/
import engine.renderer.Theme

namespace Palette

inductive Token where
  | bg | panel | line | fg | muted | accent | button | onAccent
  | accentInk | link | tint | warning | error | danger | online
  | selected | scrim | toast | toastInk | edge | badge | badgeInk
  | avatar | black | white
  deriving BEq, DecidableEq, Repr, Inhabited

def color (theme : Theme.Value) (token : Token) : UInt32 :=
  match token, theme with
  | .bg, .light => 0xf7f7f7 | .bg, .dark => 0x242424
  | .panel, .light => 0xffffff | .panel, .dark => 0x222222
  | .line, .light => 0xe5e5e5 | .line, .dark => 0x3e3e3e
  | .fg, .light => 0x222222 | .fg, .dark => 0xeaeaea
  | .muted, .light => 0x767676 | .muted, .dark => 0xb2b2b2
  | .accent, .light => 0x7647c7 | .accent, .dark => 0x2f193d
  | .button, .light => 0x7647c7 | .button, .dark => 0x521c74
  | .onAccent, _ => 0xffffff
  | .accentInk, .light => 0x7647c7 | .accentInk, .dark => 0xdbbcf0
  | .link, .light => 0x1b6fec | .link, .dark => 0x5b9bff
  | .tint, .light => 0xf9f0ff | .tint, .dark => 0x452b56
  | .warning, .light => 0x8f6900 | .warning, .dark => 0xebb449
  | .error, .light => 0xc7353b | .error, .dark => 0xf07275
  | .danger, _ => 0xc7353b
  | .online, .light => 0x0f6b3f | .online, .dark => 0x7ee2b8
  | .selected, .light => 0xf0f0f0 | .selected, .dark => 0x2f2f2f
  | .scrim, _ => 0x000000
  | .toast, .light => 0xffffff | .toast, .dark => 0x222222
  | .toastInk, .light => 0x222222 | .toastInk, .dark => 0xeaeaea
  | .edge, .light => 0x222222 | .edge, .dark => 0xeaeaea
  | .badge, _ => 0xc7353b
  | .badgeInk, _ => 0xffffff
  | .avatar, _ => 0x7647c7
  | .black, _ => 0x000000
  | .white, _ => 0xffffff

/-- Interaction tokens from the same libquiet light/dark palette. -/
def gray03 : Theme.Value → UInt32 | .light => 0xf7f7f7 | .dark => 0x242424
def gray30 : Theme.Value → UInt32 | .light => 0xb3b3b3 | .dark => 0x6f6f6f
def buttonHover : Theme.Value → UInt32 | .light => 0x5c37a0 | .dark => 0x461863

/-- libquiet avatar.ts: stable identity colours, shared by both themes. -/
def avatar (id : String) : UInt32 :=
  let colors : Array UInt32 := #[0xaf3c40, 0x9f5102, 0x786900, 0x047e39,
    0x037879, 0x4860be, 0x7252b4, 0x974391]
  let hash := id.toList.foldl (fun (h : UInt32) c => h * 31 + c.toNat.toUInt32) 0
  colors[hash.toNat % colors.size]!

end Palette
