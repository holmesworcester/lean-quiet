/- Runs actual layout, glyph rasterization, rows and composer geometry over
all supported desktop densities and phone accessibility densities. -/
import platforms.headless.Sim
import platforms.desktop.Driver
import engine.renderer.desktop.ZoomLaws

open Paint Font Row

private def require (p : Bool) (msg : String) : IO Unit :=
  unless p do throw (IO.userError msg)

private def letters (s : List UInt32) : List UInt32 :=
  (s.filter fun c => !Text.isSpace c && !Text.isInvisible c).mergeSort (· ≤ ·)

private def run : IO Unit := do
  let font ← Font.load (density := 160)
  require ((font.atSize 0).cell == 1 && (font.atSize 257).cell == 256) "rasterizer size limits"
  -- These include sizes not in the preloaded typography table.
  for size in [7, 9, 11, 13, 17, 19, 28, 37, 74, 112] do
    let f := font.atSize size
    require (f.cell == size) s!"arbitrary font size {size}"
    let some r := f.noto.chars['W'.val]? | throw (IO.userError "missing W")
    let some ink := f.noto.bitmap r | throw (IO.userError "missing raster")
    require (ink.cell == size && ink.pixels.data.any (· > 0)) "raster size/cache identity"
    let bmp := (Bitmap.blank (size*3) (size*2) (solid 0xffffff (size*3))).glyph f '龘'.val 0 0 0 false
    require (bmp.rows.any fun row => row.data.any (· == 0)) "large fallback lost its ink"
  let text := "A long message preserves every letter while wrapping. 日本語 café Ελληνικά שלום 12:30 " ++ String.ofList (List.replicate 100 'W')
  let data : RowData := {
    name := "An intentionally very long duplicate author name", text := text,
    avatar := none, time := 29330000, pics := [{ hash := .empty, w := 640, h := 480 }, { hash := .empty, w := 300, h := 900 }],
    tallies := (Row.quick.toList.map fun e => ⟨e, 999999, true⟩), pending := false, selected := false, namesake := true }
  let mut cases := 0
  for dpi in [80, 107, 120, 128, 144, 160, 176, 200, 240, 280, 320, 357, 420, 560, 640, 840, 1280] do
    let f := font.atSize (Font.pixelCell 48 dpi)
    let dm : Dim := ⟨dpi, f.cell, .light⟩
    for dp in [200, 275, 320, 390, 719, 720, 960, 1280] do
      let w := dm.px dp
      let l := Row.layout f dm w data
      let body := f.atSize (dm.px (Row.bodySize data))
      let author := f.atSize (dm.px 16)
      let stamp := f.atSize (dm.px 14)
      let tw := w - dm.textX - dm.pad
      require (l.timeX + Paint.Line.width stamp l.time ≤ w - dm.pad) s!"header overflow {dpi}/{dp}"
      -- Fractional glyph positions and advances round independently at the
      -- raster edge. Check the exact layout first, then its one-pixel bound.
      for line in Text.layout (Text.metricFont body) (Text.metricWidth tw) text do
        require (Paint.Line.width (Text.metricFont body) line ≤ Text.metricWidth tw) s!"fractional body overflow {dpi}/{dp}"
      for line in l.text do
        require (Paint.Line.width body line ≤ tw + 1) s!"body overflow {dpi}/{dp}: {Paint.Line.width body line} > {tw} + 1"
      require (letters (l.text.toList.flatMap fun line => line.toList.map (·.c)) ==
        letters (text.toList.map Char.val)) s!"body truncated {dpi}/{dp}"
      if let some (bx, _) := l.twin then
        require (dm.textX + Paint.Line.width author l.name ≤ bx.x && bx.x + bx.w ≤ l.timeX) "header overlap"
      require (l.textY ≥ dm.topPad + f.cell && l.h ≥ l.textY + Row.bodyHeight dm data l.text.size) "vertical text overlap"
      let boxes := l.pics ++ l.pills.map (·.1)
      for i in [:boxes.size] do
        let b := boxes[i]!
        require (b.x + b.w ≤ w - dm.pad && b.y + b.h ≤ l.h) s!"attachment/reaction overflow {dpi}/{dp}"
        require (b.y ≥ l.textY + Row.bodyHeight dm data l.text.size) "attachment over body text"
        for j in [i+1:boxes.size] do
          let b' := boxes[j]!
          require (b.x + b.w ≤ b'.x || b'.x + b'.w ≤ b.x || b.y + b.h ≤ b'.y || b'.y + b'.h ≤ b.y) "attachments/reactions overlap"
      let c := Composer.layout (f.atSize (dm.px 14)) dm w text 4 (dp ≥ 720) false
      for i in [:c.chips.size] do
        let (b, close) := c.chips[i]!
        require (b.x + b.w ≤ w && close.x + close.w ≤ w && b.y + b.h ≤ c.h) s!"chip overflow {dpi}/{dp}"
        for j in [i+1:c.chips.size] do
          let b' := c.chips[j]!.1
          require (b.x + b.w ≤ b'.x || b'.x + b'.w ≤ b.x || b.y + b.h ≤ b'.y || b'.y + b'.h ≤ b.y) "chips overlap"
      require (c.send.x + c.send.w ≤ w && c.send.y + c.send.h ≤ c.h) "send overflow"
      for (b, _) in c.deck do
        require (b.x + b.w ≤ c.send.x && b.y + b.h ≤ c.h) "composer actions overlap send"
      cases := cases + 1
  IO.println s!"zoom: {cases} row/composer density-width cases; arbitrary Noto sizes and large fallback pass"
  IO.println "geometry laws: zoom_identity, zoom_partition, zoom_contained, zoom_controls_screen, zoom_drawer_preserves"

def main : IO Unit := do
  try
    run
    IO.Process.exit 0
  catch e => IO.eprintln s!"zoom: {e}"; IO.Process.exit 1
