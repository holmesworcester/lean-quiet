/- Shared component pixels and the actual App.present boundary on both modes. -/
import platforms.headless.Sim
import platforms.desktop.Driver

private def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL skeleton: {label}")

private unsafe def suite (args : List String) : IO Unit := do
  let out := args[0]?.getD "out/skeleton"
  IO.FS.createDirAll out
  let sm ← Sim.new
  let app ← App.start sm.io #[780, 1600, 0, 0, 320, 0] (out ++ "/test.db") none
  let mut cases := 0
  for dpi in [160, 320, 420, 480] do
    for theme in [Theme.Value.light, .dark] do
      for logicalWidth in [1, 60, 320, 1100] do
        let dim : Row.Dim := ⟨dpi, 14 * dpi / 160, theme, none⟩
        let w := dim.px logicalWidth
        let bg := Paint.solid (Palette.color theme .bg) w
        let h : Hold.St := ⟨bg, dim, w⟩
        let n := Hold.period dim
        let rows := (Array.range (n * 3)).map (Hold.messageLine h)
        check "clipping preserves exact row widths" (rows.all (·.size == 4 * w))
        check "message repetition is density-scaled" (Hold.messageLine h 0 == Hold.messageLine h n)
        if logicalWidth ≥ 320 then
          check "avatar occupies the actual message avatar column"
            (Paint.getPx rows[dim.px 24]! (dim.pad + dim.avatar / 2) == Palette.color theme .line)
          check "rounded avatar leaves its corner clear"
            (Paint.getPx rows[dim.px 8]! dim.pad == Palette.color theme .bg)
          check "body lines align with actual message text"
            (Paint.getPx rows[dim.px 34]! (dim.textX + dim.px 8) == Palette.color theme .line)
          check "shorter second line ends before the first"
            (Paint.getPx rows[dim.px 52]! (dim.textX + min (w - dim.textX - dim.pad) (dim.px 360) * 5 / 6) == Palette.color theme .bg)
          check "author/name bar is distinct from body"
            (Paint.getPx rows[dim.px 14]! (dim.textX + dim.px 8) != Palette.color theme .line)
          writePpm (out ++ s!"/{if theme == .light then "light" else "dark"}-{dpi}-{logicalWidth}.ppm") w rows
        check "unloaded content distances retain top-down message orientation"
          (Hold.unloadedLine h (n - 1 - dim.px 14) == rows[dim.px 14]!)
        for mobile in [false, true] do
          let s := { app with io := sm.io, mobile, W := w, dim, bgRow := bg }
          for li in [0, dim.px 8, dim.px 14, dim.px 34, dim.px 52, n + 11] do
            check "desktop/mobile pending component uses shared skeleton" (App.holdLine s li == Hold.messageLine h li)
          let pending := { s with ids := #[], older := 100, newer := 100 }
          let pendingRows := App.listFrame pending 1000 #[]
          let high := 1000 + App.viewH pending + App.over
          for i in [0, pendingRows.size / 2, pendingRows.size - 1] do
            check "actual unloaded component rows match native bottom-anchored silhouettes"
              (pendingRows[i]! == Hold.unloadedLine h (high - 1 - i))
          let (_, s) ← (App.present #[] 117 false).run s
          let words ← sm.placement.get
          let plane ← sm.hold.get
          check "actual App.present publishes the density-scaled period" (words[26]!.toNat == n)
          let top := words[7]!.toNat
          let bottom := words[10]!.toNat
          check "fill plane covers viewport plus one complete message" (plane.size == bottom - top + n)
          for offset in ([-200, 0, 49, 199, 10000] : List Int) do
            for y in [top:bottom] do
              let index := (Slide.fillRowPeriod n.toUInt32 false 117 top.toUInt32 bottom.toUInt32 offset.toInt32 y.toUInt32).toNat
              let line := ((offset + bottom - 1 - y) % n).toNat
              check "native fill has the same message pixels at every signed offset"
                (index < plane.size && plane[index]! == rows[n - 1 - line]!)
          -- Keep both planes alive: a released address could be recycled.
          -- Background rows already share s.bgRow without any tile cache.
          if logicalWidth ≥ 320 then
            let row := plane[dim.px 34]!
            check "reuse probe selects actual skeleton ink" (row != bg)
            let (_, _) ← (App.present #[] 117 false).run s
            let nextPlane ← sm.hold.get
            check "actual App.present reuses cached skeleton pixel objects"
              (ptrEq row nextPlane[dim.px 34]!)
          let _ := s
        cases := cases + 1
  IO.println s!"skeleton: {cases} density/theme/width cases, desktop/mobile publication and signed native offsets passed"

unsafe def main (args : List String) : IO UInt32 := do
  try
    suite args
    (← IO.getStdout).flush
    IO.Process.exit 0
  catch e => IO.eprintln s!"{e}"; IO.Process.exit 1
