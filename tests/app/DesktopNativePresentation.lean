/- Exact native Linux publication under a private X server, plus the same
actual Driver/App/SQLite delayed-completion scenario as the host fixture. -/
import tests.app.DesktopPresentation
import platforms.desktop.Main

open Desktop Tests
@[extern "lq_test_desktop_visible"] opaque visible (b : Bool) : IO Unit
@[extern "lq_test_desktop_valid_gc"] opaque validGc (b : Bool) : IO Unit
@[extern "lq_test_desktop_unmap_queued"] opaque unmapQueued : IO Unit
@[extern "lq_test_desktop_full_input"] opaque fullInput : IO Unit

def main : IO Unit := do
  let ck ← Checks.new
  let sc ← Platform.screen
  let w := sc[0]!.toNat
  let h := sc[1]!.toNat
  let rows := Array.replicate h (Paint.solid 0x79A541 w)
  let ticket : UInt64 := 4294967297
  visible true
  let r := Publication.decode (← DesktopMain.desktopFrame rows ticket)
  ck.ok "native X publication fences the exact nonwrapped desktop ticket"
    (r.accepted && r.completed == some (ticket, 0))
  let wrong := Publication.decode (← DesktopMain.desktopFrame (rows.extract 0 (h-1)) (ticket+1))
  ck.ok "native X publication rejects a mismatched composed frame height" (!wrong.accepted && wrong.completed.isNone)
  validGc false
  let failed := Publication.decode (← DesktopMain.desktopFrame rows (ticket+2))
  validGc true
  ck.ok "an X server drawing error cannot acknowledge publication" (!failed.accepted && failed.completed.isNone)
  visible false
  let hidden := Publication.decode (← DesktopMain.desktopFrame rows (ticket+2))
  ck.ok "an unmapped native window cannot acknowledge visible presentation" (!hidden.accepted && hidden.completed.isNone)
  visible true
  fullInput
  let full := Publication.decode (← DesktopMain.desktopFrame rows (ticket+3))
  ck.ok "full input queue cannot drop the native publication completion metadata"
    (full.events.size == 4104 && full.accepted && full.completed == some (ticket+3, 0))
  unmapQueued
  let queued := Publication.decode (← DesktopMain.desktopFrame rows (ticket+4))
  ck.ok "queued native unmap behind full input cannot masquerade as visible completion"
    (!queued.accepted && queued.completed.isNone)
  visible true
  DesktopPresentationTests.run ck (some fun token picture => do
    return Publication.decode (← DesktopMain.desktopFrame picture.rows token))
  let result ← ck.finish "desktop-native-presentation"
  (← IO.getStdout).flush
  IO.Process.exit result.toUInt8
