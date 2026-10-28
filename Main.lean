/-
The app on a platform twin: the seam's externs as the app's `Io`.
-/
import Quiet

open App

def Io.platform : Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs,
   do return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, (← Platform.tzMin).toInt),
   Platform.scan, Platform.luma, Platform.log, fun t => Platform.setText t⟩

def main : IO Unit := do
  let screen ← Platform.screen
  let s ← App.spawnReader (← App.start Io.platform screen "quiet.db" (some (Link.port, false)))
  let _ ← (App.loop []).run s
