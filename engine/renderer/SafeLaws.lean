/-
Re-layout laws about the app's report handler, not a parallel state.
The old five-word protocol uses the most recent IME event; an extended
report supplies it directly. Row invalidation is tested with App.step.
-/
import App

namespace App

theorem screenChanged_size (sc : Array UInt32) (now : Nat) (s : St) :
    (screenChanged sc now s).W =
      (Safe.content { SafeFrame.report sc s.imeH with ime := {} }).w ∧
    (screenChanged sc now s).Hs = (SafeFrame.report sc s.imeH).h := by
  simp [screenChanged]

theorem screenChanged_insets (sc : Array UInt32) (now : Nat) (s : St) :
    (screenChanged sc now s).window = SafeFrame.report sc s.imeH ∧
    (screenChanged sc now s).imeH = (SafeFrame.report sc s.imeH).ime.bottom ∧
    (screenChanged sc now s).insetTop =
      (Safe.content { SafeFrame.report sc s.imeH with ime := {} }).y := by
  simp [screenChanged]

end App
