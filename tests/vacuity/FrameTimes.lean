import engine.renderer.FrameTimes

namespace Vacuity.FrameTimes

def full : Array Nat := Array.replicate 600 17000
def oversized : Array Nat := Array.replicate 900 17000

theorem nonempty :
    (FrameTimes.push full 23000).size = 301 ∧
    (FrameTimes.push full 23000).size ≤ 600 ∧
    (FrameTimes.push oversized 23000).size = 301 ∧
    (FrameTimes.push oversized 23000).size ≤ 600 := by
  refine ⟨?_, FrameTimes.bounded full 23000, ?_,
    FrameTimes.bounded oversized 23000⟩ <;>
    simp [FrameTimes.push, full, oversized]

end Vacuity.FrameTimes
