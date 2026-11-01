/- Geometry shared by the desktop painter and pointer handling. Offsets are
bottom-anchored: zero puts the thumb at the bottom, at the newest message.
The thumb is placed by rank (engine/renderer/Scrollbar.lean): `n` messages,
`k` on screen, `r` entirely below the screen. -/
import engine.renderer.desktop.Layout
import engine.renderer.Scrollbar

namespace Desktop.Scrollbar

structure Bar where
  track : Box
  thumb : Box
  range : Nat
  n : Nat
  k : Nat
  deriving Repr, Inhabited

def layout (right top height content n k r : Nat) (dpi : Nat := 160) : Option Bar :=
  let px := fun n => (n * dpi + 80) / 160
  if height == 0 || content ≤ height || right < px 16 then none else
  let k := min k n
  let r := min r (n - k)
  let size := _root_.Scrollbar.size height (px 24) n k
  let y := top + (height - size) - _root_.Scrollbar.offset height (px 24) n k r
  some ⟨⟨right - px 16, top, px 16, height⟩, ⟨right - px 9, y, px 6, size⟩, content - height, n, k⟩

/-- Keep the grabbed point under the pointer; clicks on the track centre
its thumb there. Both ends clamp, including dragging outside the window. -/
def grab (b : Bar) (x y : Nat) : Option Nat :=
  if !b.track.has x y then none
  else some (if b.thumb.y ≤ y && y < b.thumb.y + b.thumb.h then y - b.thumb.y else b.thumb.h / 2)

/-- The rank a drag seeks: the thumb's bottom is `travel - position` above
the track's bottom, and the rank is the one whose thumb lands there or below. -/
def seek (b : Bar) (grab y : Nat) : Nat :=
  let travel := b.track.h - b.thumb.h
  let position := min travel (y - min grab b.thumb.h - b.track.y)
  _root_.Scrollbar.seek travel (b.n - b.k) (travel - position)

end Desktop.Scrollbar
