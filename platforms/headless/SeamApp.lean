/- Raw input through App.step, including a page control and a drawn emoji.
Also checks the app's actual drawn offset after out-of-range OS samples. -/
import platforms.headless.Sim
open App

def demand (name : String) (ok : Bool) : IO Unit := do
  if !ok then
    IO.eprintln s!"FAIL {name}"
    IO.Process.exit 1
  IO.println s!"ok   {name}"

def feed (sm : Sim) (ts : List Input.Touch) : M Unit := do
  let serial := (← get).input.serial
  sm.raw.set (ts.foldl (fun ws t => ws ++ t.words.set! 6 serial.toUInt32) #[])
  let events ← step []
  let _ ← step (events.getD [])
  steps 3

def main : IO Unit := do
  let dir := "out/seam-app"
  IO.FS.createDirAll dir
  for suffix in ["", "-wal", "-shm"] do
    let path := s!"{dir}/quiet.db{suffix}"
    if ← System.FilePath.pathExists path then IO.FS.removeFile path
  let sm ← Sim.new
  let initial ← App.start sm.io #[1080, 2400, 128, 63, 420] s!"{dir}/quiet.db"
  let _ ← (show M Unit from do
    steps 3
    let s ← get
    let some pg := s.pageNow | throw (IO.userError "missing page")
    let some (box, _) := pg.taps.find? (·.2 == .createCommunity)
      | throw (IO.userError "missing create control")
    let x := box.x + box.w / 2
    let y := topH s + box.y + box.h / 2
    let down : Input.Touch := ⟨0, 9, ⟨x, y⟩, 100⟩
    sm.raw.set (down.words.set! 6 s.input.serial.toUInt32)
    discard <| step []
    demand "raw down belongs to the mounted page" ((← get).input.press.isSome)
    discard <| step [.background]
    discard <| step [.foreground]
    feed sm [{ down with phase := 2, time := 200 }]
    demand "release after remount cannot activate the old control"
      ((← get).page == .getStarted && (← get).input.press.isNone)
    feed sm [{ down with time := 300 }]
    sm.viewport.set #[1080, 2400, 128, 63, 421]
    discard <| step [.resize]
    feed sm [{ down with phase := 2, time := 400 }]
    demand "release after resize cannot use the old geometry"
      ((← get).page == .getStarted && (← get).input.press.isNone)
    sm.viewport.set #[1080, 2400, 128, 63, 420]
    steps 2
    feed sm [⟨0, 7, ⟨x, y⟩, 1000⟩, ⟨1, 7, ⟨x + 30, y⟩, 1050⟩, ⟨2, 7, ⟨x, y⟩, 1100⟩]
    demand "drag does not activate page control" ((← get).page == .getStarted)
    feed sm [⟨0, 7, ⟨x, y⟩, 2000⟩, ⟨0, 8, ⟨0, 0⟩, 2010⟩,
      ⟨1, 8, ⟨400, 600⟩, 2050⟩, ⟨2, 7, ⟨x + 5, y + 5⟩, 2100⟩, ⟨2, 8, ⟨400, 600⟩, 2150⟩]
    demand "first pointer's raw jitter tap opens Create" ((← get).page == .create &&
      (← get).input.lastTap == #[2, x.toUInt32, ((viewH s) - 1 - (y - topH s)).toUInt32])
    sm.cmds.modify (·.push "found seam|Ann" |>.push "channel")
    steps 3
    waitIdle sm
    for i in [0:50] do sm.cmds.modify (·.push s!"send message {i}")
    steps 5
    waitIdle sm
    demand "actual conversation has scrollable content" ((bottoms (← get)).2 > (geom (← get)).viewNow)
    sm.b.set 1000000
    steps 3
    let s ← get
    demand "app clamps its drawn offset at max" (s.b == (bottoms s).2 - (geom s).viewNow)
    sm.b.set (-1000)
    steps 3
    demand "app clamps negative OS offset to zero" ((← get).b == 0)
    sm.cmds.modify (·.push "tray 0")
    steps 3
    let s ← get
    let message := s.ids[0]!.2
    let q := Sheet.quick s.dim s.W
    let x := q.keys.left 3 + q.keys.key / 2
    let y := (geom s).composerTop + q.keys.y0 + q.keys.key / 2
    feed sm [⟨0, 4, ⟨x, y⟩, 3000⟩, ⟨2, 4, ⟨x, y⟩, 3100⟩]
    waitIdle sm
    let s ← get
    demand "raw tap selects the emoji drawn there" (s.sheet.isNone &&
      (s.rows[message]?.map (·.data.tallies) |>.getD []).any (fun t => t.emoji == Row.quick[3]! && t.mine))
    sm.cmds.modify (·.push "tray 0" |>.push "browse")
    steps 3
    let s ← get
    let some sh := s.sheet | throw (IO.userError "missing sheet")
    let cat := catOf s sh
    let x := cat.grid.x0 + cat.grid.key / 2
    let y := (geom s).composerTop + cat.grid.y0 + cat.grid.vh - cat.grid.key / 2
    feed sm [⟨0, 4, ⟨x, y⟩, 4000⟩, ⟨1, 4, ⟨x, y - 100⟩, 4050⟩,
      ⟨3, 4, ⟨x, y - 100⟩, 4100⟩]
    let s ← get
    demand "cancel ends the sheet drag without a fling"
      (s.sheet.any fun sh => sh.drag.isNone && sh.vel == 0)
    ).run initial
  IO.println "seam app: 10 checks passed"
  IO.Process.exit 0
