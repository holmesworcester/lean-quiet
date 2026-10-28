/-
The app on a platform twin: the seam's externs as the app's `Io`.
-/
import Quiet

open App

def Io.platform : Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, Platform.textClear, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs⟩

def main : IO Unit := do
  let screen ← Platform.screen
  let s ← App.start Io.platform screen "quiet.db"
  let _ ← (App.loop []).run s
