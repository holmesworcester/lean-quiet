/- The frame's timing diagnostics: a bounded sample buffer. Both App frame
paths (pages and chat) record through `push`. -/
namespace FrameTimes

/-- Keep the same 600/300 sampling policy on every screen. Even an
oversized input is reduced to the newest 300 samples before appending. -/
def push (samples : Array Nat) (elapsed : Nat) : Array Nat :=
  (if samples.size ≥ 600 then samples.extract (samples.size - 300) samples.size
   else samples).push elapsed

/-- The running frame recorder has a fixed count bound for every input. -/
theorem bounded (samples : Array Nat) (elapsed : Nat) :
    (push samples elapsed).size ≤ 600 := by
  unfold push
  split
  · simp only [Array.size_push, Array.size_extract, Nat.min_self]
    omega
  · simp only [Array.size_push]
    omega

end FrameTimes
