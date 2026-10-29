/-
Safe-area regressions on the running App.step. One database and one app
are resized repeatedly, including keyboard show/hide and side cutouts.
Screens are composed with Geometry's existing pinned/place functions.
Fixtures and their measurement limitations are in docs/SAFE.md.
-/
import platforms.headless.Sim
import engine.renderer.Toast
import engine.renderer.SafeFrame

open App Safe Paint

private def compose (sm : Sim) (s : St) : IO (Array ByteArray) := do
  let W := s.window.w
  let mut rows ← screenOf sm W s.Hs s.insetBot
  -- The IME is OS-owned. A labelled fixture in the report, not a device shot.
  if s.imeH > 0 then
    let kb := solid 0x555555 W
    for y in [s.Hs - s.imeH:s.Hs] do rows := rows.set! y kb
  return rows

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/safe"
  let render := !args.contains "--no-renders"
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    let p := dir ++ "/" ++ f
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  let report ← IO.mkRef (#[1080, 2400, 128, 63, 420, 0, 0, 0, 0, 0, 0, 0, 0] : Array UInt32)
  let now ← IO.mkRef 1000000
  let bars ← IO.mkRef (0, 0, false, false)
  let io := { sm.io with
    screen := report.get, nowUs := return (← now.get).toUInt64 * 1000,
    bars := fun t b lt lb => bars.set (t, b, lt, lb) }
  let start ← App.start io (← report.get) (dir ++ "/quiet.db")
  let count ← IO.mkRef 0
  let failures ← IO.mkRef 0
  let check (name : String) (yes : Bool) : IO Unit := do
    count.modify (· + 1)
    if !yes then failures.modify (· + 1)
    IO.println s!"{if yes then "ok" else "FAIL"} {name}"
  let (_, _) ← (show M Unit from do
    steps 2
    sm.cmds.modify (·.push "found safe")
    steps 5
    sm.cmds.modify (·.push "chaos 4")
    waitIdle sm
    let me := (← get).me
    let fixtures : Array (String × Array UInt32) := #[
      ("phone-1170-portrait", #[1170, 2532, 141, 102, 480, 0, 0, 0, 0]),
      ("phone-1170-portrait-ime", #[1170, 2532, 141, 102, 480, 0, 0, 0, 900]),
      ("phone-1170-landscape", #[2532, 1170, 0, 63, 480, 0, 141, 141, 0]),
      ("phone-1170-landscape-ime", #[2532, 1170, 0, 63, 480, 0, 141, 141, 600]),
      ("phone-1080-portrait", #[1080, 2400, 72, 63, 420, 0, 0, 0, 0, 0, 128, 0, 0]),
      ("phone-1080-portrait-ime", #[1080, 2400, 72, 63, 420, 0, 0, 0, 900, 0, 128, 0, 0]),
      ("phone-1080-landscape", #[2400, 1080, 63, 63, 420, 0, 0, 0, 0, 128, 0, 0, 0]),
      ("phone-1080-landscape-ime", #[2400, 1080, 63, 63, 420, 0, 0, 0, 550, 128, 0, 0, 0])]
    for (name, sc) in fixtures do
      report.set sc
      for (pageName, page) in [("onboarding", PageId.getStarted), ("home", .home), ("channel", .chat), ("input", .create)] do
        modify fun s => { s.withNav (Nav.reset page) with pageKey := none, chromeKey := "", sheet := none, toast := none, notices := [], me := me }
        steps 3
        let s ← get
        let i := SafeFrame.report sc
        let r := Safe.content { i with ime := {} }
        check s!"{name}/{pageName}: live report" (s.window == i && s.W == r.w && s.insetTop == r.y && s.imeH == i.ime.bottom)
        let (fr, _, _, top, bot) ← sm.last.get
        check s!"{name}/{pageName}: every row resized" ((fr ++ top ++ bot).all (·.size == 4 * i.w))
        let shot ← compose sm s
        if render then writePpm s!"{dir}/{name}-{pageName}.ppm" i.w shot
        let expected := Palette.color s.dim.theme (if page == .home || page == .chat then .panel else .bg)
        check s!"{name}/{pageName}: status ground" (r.y == 0 || getPx shot[0]! 0 == expected)
        let (tc, bc, lt, lb) ← bars.get
        check s!"{name}/{pageName}: native bar policy" (tc == expected && lt == SafeFrame.lightIcons expected && lb == SafeFrame.lightIcons bc)
        if r.x > 0 then
          check s!"{name}/{pageName}: side matches adjacent pixels" ((List.range (min s.Hs top.size)).all fun y =>
            getPx shot[y]! (r.x - 1) == getPx shot[y]! r.x)
        let before := s.page
        let _ ← onEvent (.tap .header 0 0)
        check s!"{name}/{pageName}: reserved tap rejected" ((← get).page == before)
        modify fun s => { s with toast := Toast.raise s.nowMs "Saved. Tap to dismiss." }
        steps 1
        let s ← get
        let tb := Pages.toast s.font s.dim s.W "Saved. Tap to dismiss."
        let g := geom s
        let vi : Safe.Input := ⟨s.W, s.Hs, ⟨0, s.insetTop, 0, s.insetBot⟩, {}, ⟨0, 0, 0, s.imeH⟩⟩
        let placed := Toast.layout vi ⟨0, g.top, s.W, g.viewNow⟩ (focusBox s) tb.w tb.h (SafeFrame.targetPx s.dim.dpi)
        check s!"{name}/{pageName}: toast whole or deferred" (placed.all fun e =>
          decide (e.rect.bottom ≤ g.composerTop ∧ g.top ≤ e.rect.y))
        let painted ← compose sm s
        if let some e := placed then
          check s!"{name}/{pageName}: toast pixels at proved position"
            (getPx painted[e.rect.y]! (r.x + e.rect.x + tb.w / 2) !=
              getPx shot[e.rect.y]! (r.x + e.rect.x + tb.w / 2))
          check s!"{name}/{pageName}: whole dismissal target"
            (e.rect.w ≥ s.dim.px 48 && e.rect.h ≥ s.dim.px 48 && decide (e.rect.Disjoint (focusBox s)))
        if render then writePpm s!"{dir}/{name}-{pageName}-toast.ppm" i.w painted
        now.modify (· + 3000)
        steps 1
        check s!"{name}/{pageName}: timeout on clock, no 180 frames" ((Toast.showing (← get).nowMs (← get).toast).isNone)
        let expired ← compose sm (← get)
        if let some e := placed then
          check s!"{name}/{pageName}: covered pixels uncovered after timeout"
            (getPx expired[e.rect.y]! (r.x + e.rect.x + tb.w / 2) !=
              getPx painted[e.rect.y]! (r.x + e.rect.x + tb.w / 2))
      -- An actual selected message opens the actual sheet painter.
      modify fun s => { s.withNav (Nav.reset .chat) with toast := none }
      steps 3
      modify fun s => { s with selected := s.ids[0]?.map (·.2), sheet := some {}, chromeKey := "" }
      steps 2
      if render then writePpm s!"{dir}/{name}-sheet.ppm" sc[0]!.toNat (← compose sm (← get))
      let (_, bottom, _, _) ← bars.get
      check s!"{name}/sheet: bottom ground" (bottom == Palette.color (← get).dim.theme .panel)
    -- A cutout can exchange sides without changing content width. A
    -- pointer acquired before that move must not activate the moved page.
    report.set #[1080, 2400, 128, 63, 420, 0, 100, 0, 0]
    openPage .getStarted
    steps 3
    let before ← get
    let some pg := before.pageNow | throw (IO.userError "missing onboarding page")
    let some (box, _) := pg.taps.find? (·.2 == .createCommunity)
      | throw (IO.userError "missing Create control")
    let down : Input.Touch := ⟨0, 5, ⟨100 + box.x + box.w/2, topH before + box.y + box.h/2⟩, 100⟩
    sm.raw.set (down.words.set! 6 before.input.serial.toUInt32)
    discard <| step []
    check "equal-width cutout test has an active pointer" ((← get).input.press.isSome)
    report.set #[1080, 2400, 128, 63, 420, 0, 0, 100, 0]
    discard <| step []
    check "equal-width cutout shift revokes old pointer" ((← get).W == before.W && (← get).input.press.isNone)
    let up := { down with phase := 2, time := 200 }
    sm.raw.set (up.words.set! 6 (← get).input.serial.toUInt32)
    let events ← step []
    discard <| step (events.getD [])
    check "release after cutout shift does not activate moved control" ((← get).page == .getStarted)
    let serial := (← get).input.serial.toUInt32
    sm.events.set (down.words.set! 6 serial ++ up.words.set! 6 serial)
    report.set #[1080, 2400, 128, 63, 420, 0, 100, 0, 0]
    let generation := (← get).life.generation
    discard <| step []
    check "same-poll tap is revoked when safe origin changes"
      ((← get).page == .getStarted && (← get).life.generation > generation)
    -- A queued keyboard event must not overwrite the new snapshot.
    report.set #[1080, 2400, 128, 63, 420, 0, 0, 0, 900]
    let _ ← step [.ime 0]
    check "new IME report outranks stale event" ((← get).imeH == 900)
    report.set #[1080, 2400, 128, 63, 420, 0, 0, 0, 0]
    steps 1
    check "keyboard hide restores viewport" ((← get).imeH == 0)
    say "Dismiss this"
    onTap .list 0 0 false
    check "tap dismisses the transient card" ((← get).toast.isNone)
    modify fun s => { s with sheet := some {}, text := "Must not send below a surface" }
    let _ ← onEvent .send
    check "surface blocks keyboard Send to lower layer" ((← get).text == "Must not send below a surface")
    check "icon style follows the colour, both polarities" (SafeFrame.lightIcons 0 && !SafeFrame.lightIcons 0xffffff)
    -- No space, asymmetric cutouts and changes in navigation mode.
    let bad : Safe.Input := ⟨40, 30, ⟨25, 20, 25, 20⟩, {}, {}⟩
    check "oversized insets: no target accepted" ((Safe.target bad ⟨0, 0, 1, 1⟩).isNone)
    check "keyboard intersects: whole target rejected" ((Safe.target ⟨1080, 2400, {}, {}, ⟨0, 0, 0, 900⟩⟩ ⟨20, 1490, 100, 100⟩).isNone)
    check "toast cannot cover focused input" ((Toast.layout ⟨100, 100, {}, {}, {}⟩ ⟨0, 0, 100, 100⟩ ⟨0, 0, 100, 100⟩ 50 50).isNone)
    check "Chrome cannot cover Page" ((Occlusion.place ⟨100, 100, {}, {}, {}⟩ ⟨.chrome, ⟨0, 0, 50, 50⟩⟩ ⟨.page, ⟨0, 0, 100, 100⟩⟩ false ⟨0, 0, 0, 0⟩).isNone)
    check "surface makes Page inert" (!Occlusion.active true .page && Occlusion.active true .surface)
    check "dismissed toast is gone" ((Toast.showing (← get).nowMs none).isNone)
    ).run start
  IO.println s!"{← count.get} checks, {← failures.get} failures; renders in {dir}"
  IO.Process.exit (if (← failures.get) == 0 then 0 else 1)
