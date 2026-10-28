/-
The app on a platform twin: the seam's externs as the app's `Io`.
-/
import Quiet.PlatformIo

open App

def main : IO Unit := do
  let screen ← Platform.screen
  let s ← App.start Io.platform screen "quiet.db" (some (Link.port, false))
  let _ ← (App.loop []).run s
