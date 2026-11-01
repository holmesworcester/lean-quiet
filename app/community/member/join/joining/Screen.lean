import engine.renderer.Page

/-!
Waiting to join: where the request went, and what it waits for.
-/

namespace Pages
open Paint Text Font Row

/-- One step of the waiting card's rail: done, now, or next. -/
inductive Beat where | done | now | next
  deriving BEq, Inhabited

/-- Waiting to be let in: the mark, the title and lead, and one card per
wait: the community's short id (a link carries no name), the rail, and
Stop waiting; then the footer. -/
def waiting {α : Type} [BEq α] [Inert α] (onStop : α) (f : Font) (dm : Dim) (W h : Nat) (id8 : String) (beats : Array (String × String × Beat))
    (doing : Array String) : PageOf α := Id.run do
  let px := dm.px
  let f := f.atSize (px 14)
  let hint := f.atSize (px 13)
  let title := (f.atSize (px 17)).medium
  let dm := { dm with cell := px 14 }
  -- .centered: a 24rem column including 1.5rem gutters, on every platform.
  let column := min W (px 384)
  let x0 := (W - column) / 2 + px 24
  let x1 := W - x0
  let tw := x1 - x0 - px 64
  let rowsH := beats.foldl (fun n (t, sub, _) => n +
    (Text.layout f tw t).size * dm.lineH + px 2 +
    (Text.layout hint tw sub).size * px 19 + px 14) 0
  let contentH := px 54 + px 24 + title.cell + px 12 + f.cell + px 24 +
    px 64 + px 16 + rowsH + doing.size * dm.lineH +
    (if doing.isEmpty then 0 else px 12) + px 44 + px 24 + px 40
  let y0 := max (px 32) ((h - contentH) / 2)
  let d := px 54
  let mut b := blank W h dm.theme
  b := b.icon f "quiet-mark" ((W - d) / 2) y0 d (Palette.color dm.theme .accentInk)
  let mut y := y0 + d + dm.px 24
  b := centred title b "Waiting to be let in" y (Palette.color dm.theme .fg) true
  y := y + title.cell + dm.px 12
  b := centred f b "Someone already inside has to let you in." y (Palette.color dm.theme .muted)
  y := y + f.cell + dm.px 24
  -- the (Palette.color dm.theme .panel)
  let cy := y
  let headH := dm.px 64
  let mut ry := cy + headH + dm.px 16
  let mut rows : Array (Nat × String × String × Beat × Nat) := #[]
  for (t, sub, beat) in beats do
    let ts := Text.layout f tw t
    let ls := Text.layout hint tw sub
    rows := rows.push (ry, t, sub, beat, ts.size)
    ry := ry + ts.size * dm.lineH + dm.px 2 + ls.size * px 19 + dm.px 14
  let doingY := ry
  ry := ry + doing.size * dm.lineH + (if doing.isEmpty then 0 else dm.px 12)
  let stopY := ry
  let cardEnd := stopY + dm.px 44
  b := b.round x0 cy x1 cardEnd (dm.px 12) (Palette.color dm.theme .line)
  b := b.round (x0 + px 1) (cy + px 1) (x1 - px 1) (cardEnd - px 1) (dm.px 12 - px 1) (Palette.color dm.theme .panel)
  -- head: the avatar of the id, the id, the caption
  let av := dm.px 36
  b := b.round (x0 + dm.px 16) (cy + (headH - av) / 2) (x0 + dm.px 16 + av) (cy + (headH + av) / 2) (dm.px 6) (Palette.avatar id8)
  b := b.line f (oneLine f f.cell (String.ofList (id8.toList.take 2))) (x0 + dm.px 16 + (av - f.cell) / 2) (cy + (headH - f.cell) / 2) (Palette.color dm.theme .fg)
  let tx := x0 + dm.px 16 + av + dm.px 12
  b := b.line f (oneLine f (x1 - tx) s!"<{id8}>") tx (cy + dm.px 8) (Palette.color dm.theme .fg)
  b := b.line hint (oneLine hint (x1 - tx - dm.px 8) "Its name arrives with the first sync") tx (cy + dm.px 8 + f.cell) (Palette.color dm.theme .muted)
  b := b.fill (x0 + 2) (cy + headH) (x1 - 2) (cy + headH + 2) (Palette.color dm.theme .line)
  -- the rail
  let mx := x0 + dm.px 15
  let mr := dm.px 9
  for i in [0:rows.size] do
    let (by0, t, sub, beat, tl) := rows[i]!
    let mcy := by0 + f.cell / 2
    if i + 1 < rows.size then
      b := b.fill (mx + mr - 1) (mcy + mr) (mx + mr + 1) (rows[i+1]!.1 + f.cell / 2 - mr) (Palette.color dm.theme .line)
    match beat with
    | .done =>
      b := b.round mx (mcy - mr) (mx + 2 * mr) (mcy + mr) mr (Palette.color dm.theme .accentInk)
      b := b.line f (oneLine f f.cell "✓") (mx + mr - f.cell / 4) (mcy - f.cell / 2) (Palette.color dm.theme .onAccent)
    | .now =>
      b := b.round mx (mcy - mr) (mx + 2 * mr) (mcy + mr) mr (Palette.color dm.theme .accentInk)
      b := b.round (mx + 3) (mcy - mr + 3) (mx + 2 * mr - 3) (mcy + mr - 3) (mr - 3) (Palette.color dm.theme .panel)
      b := b.round (mx + mr - 4) (mcy - 4) (mx + mr + 4) (mcy + 4) 4 (Palette.color dm.theme .accentInk)
    | .next =>
      b := b.round mx (mcy - mr) (mx + 2 * mr) (mcy + mr) mr (Palette.color dm.theme .line)
      b := b.round (mx + 3) (mcy - mr + 3) (mx + 2 * mr - 3) (mcy + mr - 3) (mr - 3) (Palette.color dm.theme .panel)
    let rx := mx + 2 * mr + dm.px 12
    let ts := Text.layout f (x1 - rx - dm.px 16) t
    for k in [0:ts.size] do
      b := b.line f ts[k]! rx (by0 + k * dm.lineH) (if beat == .now then (Palette.color dm.theme .accentInk) else if beat == .done then (Palette.color dm.theme .fg) else (Palette.color dm.theme .muted)) (beat != .next)
    let hints := Text.layout hint (x1 - rx - dm.px 15) sub
    for k in [0:hints.size] do
      b := b.line hint hints[k]! rx (by0 + tl * dm.lineH + px 2 + k * px 19) (Palette.color dm.theme .muted)
  for i in [0:doing.size] do
    b := b.line f (oneLine f (x1 - x0 - dm.px 32) doing[i]!) (x0 + dm.px 16) (doingY + i * dm.lineH) (Palette.color dm.theme .muted)
  b := b.fill (x0 + 2) stopY (x1 - 2) (stopY + 2) (Palette.color dm.theme .line)
  if dm.hot x0 stopY (x1 - x0) (dm.px 44) then b := b.fill (x0 + 2) (stopY + 2) (x1 - 2) (stopY + dm.px 44 - 2) (Palette.color dm.theme .selected)
  b := centred f b "Stop waiting" (stopY + (dm.px 44 - f.cell) / 2) (Palette.color dm.theme .muted)
  let fy := cardEnd + dm.px 24
  let (b3, _) := para f dm b "You can close Quiet. This picks up where it left off." x0 fy (x1 - x0) (Palette.color dm.theme .muted)
  return ⟨b3, #[(⟨x0, stopY, x1 - x0, dm.px 44⟩, onStop)]⟩

end Pages
