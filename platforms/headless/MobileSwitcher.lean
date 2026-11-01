/- Exercise the shared phone sheet at native densities, including its real
input dispatch and native scroll extent. Pixel references run separately. -/
import platforms.headless.Sim

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"mobile switcher: {name}")

private def suite : IO Unit := do
  let sm ← Sim.new
  let base ← App.start sm.io #[780, 1600, 0, 0, 320, 0] "out/mobile-switcher/test.db" none
  for dpi in [160, 320, 420, 480] do
    for theme in [Theme.Value.light, .dark] do
      for width in [320, 390, 430] do
        let dm : Row.Dim := ⟨dpi, 16 * dpi / 160, theme, none⟩
        let px := dm.px
        let w := px width
        let entries : Array Pages.Entry := #[⟨"Same name", "abcdef1234", 0, false, false⟩,
          ⟨"Same name", "fedcba1234", 0, true, false⟩,
          ⟨"Pending", "abc1234567", 0, false, true⟩]
        let pg := Pages.switcher Pages.Act.switchTo Pages.Act.addMembers Pages.Act.communitySettings Pages.Act.joinCommunity Pages.Act.createCommunity Pages.Act.stub Pages.Act.back base.font dm w (px 580) entries 0 true
        let pw := Pages.switcherWidth dm w
        check "56dp outside dismissal strip" (w - pw ≥ px 56)
        check "current account first, duplicate labels preserve identity" (pg.hit (px 80) (px 30) == .switchTo 1)
        check "other same-name account is selectable" (pg.hit (px 80) (px 90) == .switchTo 0)
        check "pending community cannot be selected" (pg.hit (px 80) (px 150) == .none)
        check "invite target" (pg.hit (pw - px 68) (px 37) == .addMembers)
        check "settings target" (pg.hit (pw - px 28) (px 37) == .communitySettings)
        check "outside dismisses" (pg.hit (w - 1) (px 100) == .back)
        check "avatar uses full identity color" (Paint.getPx pg.bmp.rows[px 25]! (px 22) == Palette.avatar "fedcba1234")
        let many := (Array.range 24).map fun i => { entries[0]! with name := s!"Community {i}", current := i == 0 }
        let long := Pages.switcher Pages.Act.switchTo Pages.Act.addMembers Pages.Act.communitySettings Pages.Act.joinCommunity Pages.Act.createCommunity Pages.Act.stub Pages.Act.back base.font dm w (px 580) many 0 true
        let s := { App.openSt .switcher base with
          W := w, Hs := px 640, dim := dm,
          insetTop := 0, insetBot := 0, pageNow := some long }
        check "native scroll extent includes all communities and actions" (App.scrollHeight s == long.bmp.h && App.scrollHeight s > App.viewH s)
        let y := px (8 + 24 * 58 + 16 + 2 * 58 + 29)
        check "linked devices below the fold is hit-testable" (long.hit (px 80) y == .stub "Linked devices")
        let (_, after) ← (App.onTap .list (px 80) (long.bmp.h - 1 - y) false).run s
        check "actual bottom-anchored input reaches linked devices" (after.page == .stub && after.labelText == "Linked devices")
        -- Switcher → gear → back draws the switcher over the backdrop it
        -- opened with. 566e566 emptied it on the gear; NavLaws.back_open
        -- caught that (docs/CAUGHT.md).
        let backdrop := #[ByteArray.mk #[1, 2, 3, 4], ByteArray.mk #[5, 6]]
        let sb := { s with switcherBackdrop := backdrop }
        check "settings target on the long sheet" (long.hit (pw - px 28) (px 37) == .communitySettings)
        let (_, gear) ← (App.onTap .list (pw - px 28) (long.bmp.h - 1 - px 37) false).run sb
        check "gear opens community settings" (gear.page == .communitySettings)
        let (_, back) ← (App.onTap .header (px 20) (px 20) false).run gear
        check "back from settings returns to the switcher with its backdrop"
          (back.page == .switcher && back.switcherBackdrop.map (·.data) == backdrop.map (·.data))
        let (_, closed) ← (App.onTap .header (w - 1) (px 20) false).run s
        check "outside header dismisses actual page" (closed.page != .switcher)
        let bar := Pages.switcherBar base.font dm w (px 24)
        check "native inset plus 60dp header" (bar.h == px 24 + px 60)
  IO.println "mobile switcher: 24 density/theme/width cases, duplicate identities, pending joins, controls, native extent and actual tap dispatch passed"

def main : IO UInt32 := do
  try
    IO.FS.createDirAll "out/mobile-switcher"
    suite
    (← IO.getStdout).flush
    IO.Process.exit 0
  catch e =>
    IO.eprintln (toString e)
    IO.Process.exit 1
