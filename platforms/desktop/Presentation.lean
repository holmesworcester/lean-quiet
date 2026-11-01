/- Acknowledgement is attached to the actual desktop publication seam. App
layer collection alone cannot release a composer obligation. -/
import platforms.desktop.Driver

namespace Desktop

private def currentCandidate (s : App.St) (p : App.PresentationCandidate) : Bool := Id.run do
  let some e := s.ownSends.head | return false
  let some row := s.rows[e.message.2]? | return false
  return s.page == .chat && s.sheet.isNone && e.message.2 == p.message &&
    s.life.generation == p.generation &&
    row.paintFlight.map (·.handle.ticket) == some p.ticket &&
    row.shownCommitted && !row.data.pending && row.shown.isSome && row.task.isNone &&
    row.painted.1 == row.ver

/-- Compare actual body ink, allowing the desktop's unrelated background,
shadow and avatar decoration. The mask comes from the retained committed
bitmap; expected colors come from the exact row paint used by the desktop.
Photo-only sends compare the actual preview rectangle instead. Work is
restricted to the one cached content band, never the complete message. -/
private def bodyMatches (s : App.St) (row : App.RowSt) (bodyY : Nat)
    (expected actual : Array ByteArray) : Bool := Id.run do
  if expected.isEmpty || expected.size != actual.size then return false
  if let some box := row.lay.pics[0]? then
    if bodyY == box.y then
      return box.w > 0 && (expected.zip actual).all (fun (e, a) =>
        e.extract (4*box.x) (4*(box.x+box.w)) == a.extract (4*box.x) (4*(box.x+box.w)))
  let some original := row.shown | return false
  let ground := if row.data.selected then Paint.solid (Palette.color s.dim.theme .selected) s.W
    else s.bgRow
  let mut left := s.W
  let mut right := 0
  for j in [0:expected.size] do
    let source := (original.rows[bodyY+j]?).getD .empty
    for x in [s.dim.textX:s.W-s.dim.pad] do
      if Paint.getPx source x != Paint.getPx ground x then
        left := min left x
        right := max right (x+1)
  if left ≥ right then return false
  -- Include surrounding/background pixels, preserving glyph contrast as
  -- well as ink. A solid rectangle cannot stand in for rendered letters.
  let lo := left-1
  let hi := min s.W (right+1)
  return (expected.zip actual).all (fun (e, a) =>
    e.extract (4*lo) (4*hi) == a.extract (4*lo) (4*hi))

/-- Check the cached actual content band against the final composed desktop
pixels, including drawers, popups, hover decoration and their clipping. -/
def qualifying (d : Driver) (ls : Layers) (picture : Paint.Bitmap)
    (rendered : Option (Engine.Id × Paint.Bitmap)) : Option App.PresentationCandidate := do
  if d.ui.switching || d.ui.context != .closed then none else do
    let p ← d.app.presenting
    if p.frame != ls.publication || !currentCandidate d.app p then none else do
      let row ← d.app.rows[p.message]?
      let bottom ← App.rowBottom d.app p.message
      let (bodyY, bodyH) ← App.presentationBand d.app row
      let bitmap ← (rendered.filter (fun r => r.1 == p.message)).map Prod.snd <|> row.shown
      let bodyTop := bottom + row.lay.h - bodyY
      let frameRow := ls.over + (d.app.b + App.viewH d.app - bodyTop)
      let lo := (ls.placement[0]?).getD 0 |>.toNat
      let hi := (ls.placement[1]?).getD 0 |>.toNat
      let y := ((ls.placement[2]?).getD 0).toNat + frameRow - lo
      let x := d.layout.main.x * 4
      let body := bitmap.rows.extract bodyY (bodyY + bodyH)
      if body.isEmpty || frameRow < lo || frameRow + body.size > hi || y + body.size > picture.rows.size then none else
        if bodyMatches d.app row bodyY body
          ((picture.rows.extract y (y + body.size)).map fun r => r.extract x (x + d.app.W * 4))
        then some p else none

/-- The actual runner and tests call this same publication/acknowledgement
step. An older tracked candidate survives rejected staging and accepted untracked redraws. -/
def publish (d : Driver) (display : UInt64 → Paint.Bitmap → IO Publication.Result)
    (nativeScroll : Bool := false) : IO (Driver × Array UInt32) := do
  let ls ← d.layers.get
  let (picture, rendered) ← Desktop.pictureWithRow d nativeScroll
  let candidate := qualifying d ls picture rendered
  let result ← display ls.publication picture
  let prior := d.presenting.filter (currentCandidate d.app)
  let candidate := if result.accepted && result.tracking == some ls.publication then candidate else none
  let receipt (p : Option App.PresentationCandidate) :=
    App.Presentation.acknowledge (p.map fun p => (p.frame, p.message))
      ((result.completed.filter fun r => r.2 == 0).map Prod.fst)
  let acknowledged := (receipt prior <|> receipt candidate)
  let d := if d.app.ownSends.head.any (fun e => acknowledged == some e.message.2) then
      { d with presenting := none, app := { d.app with ownSends := d.app.ownSends.pop, presenting := none } }
    else { d with presenting :=
      if prior.any (fun p => result.tracking == some p.frame) || result.tracking.isNone
      then prior else candidate }
  return (d, Publication.forInput result)

end Desktop
