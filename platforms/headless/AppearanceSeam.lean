/- The native headless shell and the real app loop, with an explicit end
after the script closes its window. No network node is needed. -/
import engine.renderer.PlatformIo

def main : IO Unit := do
  let screen ← Platform.screen
  let s ← App.start App.Io.platform screen "quiet.db"
  let _ ← (App.loop []).run s
  IO.Process.exit 0
