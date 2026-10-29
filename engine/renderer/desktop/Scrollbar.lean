/- Geometry shared by the desktop painter and pointer handling. Offsets are
bottom-anchored: zero puts the thumb at the bottom, at the newest message. -/
import engine.renderer.desktop.Layout

namespace Desktop.Scrollbar

structure Bar where
  track : Box
  thumb : Box
  range : Nat
  deriving Repr, Inhabited

def layout (right top height content offset : Nat) : Option Bar :=
  if height == 0 || content ≤ height || right < 16 then none else
  let thumbH := min height (max 24 (height * height / content))
  let range := content - height
  let travel := height - thumbH
  let y := top + travel - min travel (min offset range * travel / range)
  some ⟨⟨right - 16, top, 16, height⟩, ⟨right - 9, y, 6, thumbH⟩, range⟩

/-- Keep the grabbed point under the pointer; clicks on the track centre
its thumb there. Both ends clamp, including dragging outside the window. -/
def grab (b : Bar) (x y : Nat) : Option Nat :=
  if !b.track.has x y then none
  else some (if b.thumb.y ≤ y && y < b.thumb.y + b.thumb.h then y - b.thumb.y else b.thumb.h / 2)

def offset (b : Bar) (grab y : Nat) : Nat :=
  let travel := b.track.h - b.thumb.h
  let position := min travel (y - min grab b.thumb.h - b.track.y)
  if travel == 0 then 0 else (travel - position) * b.range / travel

end Desktop.Scrollbar
