/- The actual desktop staging/picture/publication path, with controlled native
API completion. No native completion is inferred from Desktop.tick alone. -/
import platforms.desktop.Presentation
import platforms.headless.Sim
import tests.engine.Checks

open App Desktop Engine Data Tests

namespace DesktopPresentationTests

def run (ck : Checks)
    (native : Option (UInt64 → Paint.Bitmap → IO Publication.Result) := none) : IO Unit := do
  let dir := s!"out/desktop-presentation/{← IO.Process.getPID}"
  IO.FS.createDirAll dir
  let sm ← Sim.new
  let mut d ← Desktop.start sm.io 1100 760 (dir ++ "/quiet.db")
  let (_, s) ← (App.found "Desktop publication" "Alice").run d.app
  d := { d with app := s }
  for _ in [0:30] do d ← Desktop.tick d; IO.sleep 2
  let (_, s) ← (show App.M Unit from do
    App.openPage .chat
    modify fun s => { s with text := "An own send needs actual desktop publication" }
    App.sendNow).run d.app
  d := { d with app := s }
  let some own := d.app.ownSends.head | throw (IO.userError "desktop own-send obligation missing")
  let id := own.message.2
  for _ in [0:300] do
    d ← Desktop.tick d
    if d.app.presenting.isSome then break
    IO.sleep 2
  for _ in [0:5] do d ← Desktop.tick d; IO.sleep 2
  ck.ok "desktop App layer staging never acknowledges an unpresented committed own send"
    (d.app.ownSends.contains id && d.app.rows[id]?.any (fun r => r.shownCommitted && !r.data.pending) &&
     d.app.presenting.isSome && d.presenting.isNone && (← sm.frames.get) == 0)
  let (rejected, _) ← Desktop.publish d fun _ _ => pure {}
  d := rejected
  ck.ok "a rejected actual desktop publication creates no completion candidate"
    (d.app.ownSends.contains id && d.presenting.isNone)
  let ls ← d.layers.get
  let (picture, rendered) ← Desktop.pictureWithRow d
  let covered := picture.fill d.layout.main.x (App.topH d.app)
    (d.layout.main.x + d.app.W) (d.height - App.botH d.app) (Palette.color d.app.dim.theme .fg)
  ck.ok "an opaque overlay over the actual text cannot acknowledge presentation"
    ((Desktop.qualifying d ls covered rendered).isNone)
  let obscured := { d with ui := { d.ui with switching := true } }
  let (obscured, _) ← Desktop.publish obscured fun ticket _ =>
    pure { accepted := true, tracking := some ticket, completed := some (ticket, 0) }
  ck.ok "an overlaid desktop popup cannot acknowledge the inactive conversation"
    (obscured.app.ownSends.contains id && obscured.presenting.isNone)
  let some top := Desktop.messageTop d.app d.height id | throw (IO.userError "hovered message position missing")
  let some row := d.app.rows[id]? | throw (IO.userError "hovered message row missing")
  let hover := Desktop.pointerEvent d (.motion (d.layout.main.x + d.app.dim.px 60)
    (top.toNat + row.lay.textY + max 1 (d.app.dim.lineH / 2)))
  let (hover, _) ← Desktop.publish hover fun ticket _ =>
    pure { accepted := true, tracking := some ticket, completed := some (ticket, 0) }
  ck.ok "actual desktop hover styling still acknowledges its visible committed body"
    ((Desktop.hoveredRow d.layout d.height hover.ui d.app).any (fun r => r.1 == id) &&
      !hover.app.ownSends.contains id)
  let (pending, _) ← Desktop.publish d fun ticket _ => pure { accepted := true, tracking := some ticket }
  d := pending
  let some candidate := d.presenting | throw (IO.userError "desktop composed content did not qualify")
  ck.ok "accepted desktop API staging retains one candidate without acknowledging completion"
    (candidate.frame == ls.publication && d.app.ownSends.contains id)
  for _ in [0:5] do
    d ← Desktop.tick d
    let (next, _) ← Desktop.publish d fun _ _ => pure {}
    d := next
  ck.ok "five newer App staging frames cannot replace a delayed accepted desktop candidate"
    (d.presenting.any (fun p => p.frame == candidate.frame) &&
     (← d.layers.get).publication > candidate.frame && d.app.ownSends.contains id)
  for _ in [0:5] do
    d ← Desktop.tick d
    let (next, events) ← Desktop.publish d fun _ _ =>
      pure { accepted := true, tracking := some candidate.frame, events := #[2, 70, 90, 0] }
    d := next
    ck.ok "accepted newer redraw keeps its input while an older completion is tracked"
      (events == #[2, 70, 90, 0] && d.presenting.any (·.frame == candidate.frame) && d.app.ownSends.contains id)
  let (refused, events) ← Desktop.publish d fun _ _ =>
    pure { events := #[2, 70, 90, 0, 4, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0] }
  d := refused
  ck.ok "refused geometry drops stale pointer actions, keeps text keys and close, and cancels gestures"
    (events == #[4, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 16, 0, 0, 1])
  let before ← d.app.wr.count.get
  let mut admitted := true
  for emoji in ["👍", "💚", "🌱", "🙂", "🎉"] do
    let (ok, s) ← (App.reactTo id emoji).run d.app
    admitted := admitted && ok
    d := { d with app := s }
    for _ in [0:12] do d ← Desktop.tick d; IO.sleep 2
    let (next, _) ← Desktop.publish d fun _ _ => pure {}
    d := next
  ck.ok "five actual signed reaction writes commit while desktop completion is delayed"
    (admitted && (← d.app.wr.count.get) ≥ before + 5)
  ck.ok "cosmetic churn retains the exact committed raster ticket until native completion"
    (d.app.rows[id]?.any (fun r => r.paintFlight.any (·.handle.ticket == candidate.ticket) &&
      r.task.isNone && r.shownCommitted) && d.presenting.any (·.frame == candidate.frame))
  let (shifted, _) ← Desktop.publish d fun _ _ =>
    pure { completed := some (candidate.frame, 900) }
  d := shifted
  ck.ok "a completed desktop frame translated away from the content does not acknowledge it"
    (d.app.ownSends.contains id)
  let (completed, _) ← Desktop.publish d fun _ _ =>
    pure { completed := some (candidate.frame, 0) }
  d := completed
  ck.ok "the delayed native completion releases exactly its retained visible committed send"
    (!d.app.ownSends.contains id && d.presenting.isNone)
  let (_, s) ← (show App.M Unit from do
    modify fun s => { s with text := "Cancel demand when opening the wide settings pane" }
    App.sendNow).run d.app
  d := { d with app := s }
  ck.ok "second actual composer action has a presentation obligation" (!d.app.ownSends.entries.isEmpty)
  d ← Desktop.act d .settings
  ck.ok "wide desktop drawer navigation cancels visibility demand while preserving its write"
    (d.ui.context == .settings && d.app.ownSends.entries.isEmpty && !d.app.queuedWrites.isEmpty)
  d ← Desktop.act d .close
  let (_, s) ← (show App.M Unit from do
    modify fun s => { s with text := "" }
    App.attachSamplePhoto
    App.sendNow).run d.app
  d := { d with app := s }
  let some photo := d.app.ownSends.head | throw (IO.userError "desktop photo obligation missing")
  for _ in [0:300] do
    d ← Desktop.tick d
    if d.app.presenting.isSome then break
    IO.sleep 2
  let (photoDone, _) ← Desktop.publish d fun ticket _ =>
    pure { accepted := true, tracking := some ticket, completed := some (ticket, 0) }
  d := photoDone
  ck.ok "a desktop photo-only send acknowledges its actual decoded preview rectangle"
    (!d.app.ownSends.contains photo.message.2 && d.app.rows[photo.message.2]?.any (fun r =>
      r.data.text.isEmpty && r.painted.2[1]?.getD false &&
      (App.presentationBand d.app r).any (fun b => r.lay.pics[0]?.any (·.y == b.1))))
  if let some display := native then
    let (_, s) ← (show App.M Unit from do
      modify fun s => { s with text := "The actual X server must complete this desktop publication" }
      App.sendNow).run d.app
    d := { d with app := s }
    let some third := d.app.ownSends.head | throw (IO.userError "native send missing")
    for _ in [0:300] do
      d ← Desktop.tick d
      if d.app.presenting.isSome then break
      IO.sleep 2
    ck.ok "the actual Linux publication starts with an unacknowledged committed body"
      (d.app.ownSends.contains third.message.2 && d.app.presenting.isSome)
    let (next, _) ← Desktop.publish d display
    d := next
    ck.ok "actual X server completion acknowledges the composed committed body"
      (!d.app.ownSends.contains third.message.2)
  d.app.raster.reconcile []

def main : IO Unit := do
  let ck ← Checks.new
  try DesktopPresentationTests.run ck
  catch e =>
    IO.eprintln s!"desktop fixture: {e}"
    ck.ok "desktop scenario completed" false
  let result ← ck.finish "desktop-presentation"
  (← IO.getStdout).flush
  IO.Process.exit result.toUInt8

end DesktopPresentationTests
