/- The actual App.step, threaded SQLite reader and asynchronous paints.
The measured loop uses the pre-scheduler public API for before/after
comparisons. The separate 1536px native-buffer check intentionally rejects
the old overscan margin. No fake frame clock; CSV records frame/row latency,
not whether every image inside a completed row has decoded. -/
import platforms.headless.Sim

open App Engine Community Data

namespace Scrolling

/-- Pixels of visible message geometry without a completed row bitmap.
Also counts unloaded parts of the viewport, which a mounted-row-only
counter would miss precisely when a fling outruns the reader. -/
def missing (s : St) : Nat := Id.run do
  let (bots, ch) := bottoms s
  let lo := max bottomPad s.b
  let hi := min (ch - 16) (s.b + viewH s)
  let mut painted := 0
  for i in [0:s.ids.size] do
    let x := s.ids[i]!.2
    let bot := bots[i]!
    if let some row := s.rows[x]? then
      if let some bmp := row.shown then
        let h := min bmp.h row.lay.h
        painted := painted + (min hi (bot + h) - max lo bot)
  return hi - lo - painted

def run (dir : String) (backlog : Bool) : IO UInt32 := do
  IO.FS.createDirAll dir
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/quiet.db" ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let ((), prepared) ← (show M Unit from do
    sm.cmds.modify (·.push "found scroll-fixture|Reader")
    steps 3
    waitIdle sm
    sm.cmds.modify (·.push "channel")
    steps 2
    sm.cmds.modify (·.push "chaos 500")
    waitIdle sm).run initial
  -- Sample the already prepared pixels 1536 px ahead without running
  -- another UI frame. This is the native compositor outrunning one frame.
  let ((), prepared) ← (show M Unit from do
    let deadline := (← IO.monoMsNow) + 5000
    while missing { (← get) with b := 1536 } > 0 && (← IO.monoMsNow) < deadline do
      steps 1
      IO.sleep 2
    let s ← get
    sm.b.set 1536
    let composed ← screenOf sm s.W s.Hs s.insetBot
    sm.b.set 0
    let expected := listFrame s 1536 (bottoms s).1
    let pixelsMatch := (List.range (geom s).viewNow).all fun y =>
      composed[(geom s).top + y]? == expected[over + y]?
    if missing { s with b := 1536 } > 0 || !pixelsMatch then
      throw (IO.userError "text overscan cannot cover a 1536px native scroll without a new frame")
    ).run prepared
  let initial ← App.spawnReader prepared
  -- Fault injection: unrelated background tasks occupy the shared pool
  -- while the user scrolls. Reader IO and native input remain runnable.
  -- Old paints queued into this pool accumulate; current component work
  -- has its own bounded worker and retires abandoned requests.
  let release ← IO.mkRef false
  let entered ← IO.mkRef 0
  let mut blockers := #[]
  if backlog then
    for _ in [0:2] do
      blockers := blockers.push (← IO.asTask do
        entered.modify (· + 1)
        while !(← release.get) do IO.sleep 1)
    let deadline := (← IO.monoMsNow) + 5000
    while (← entered.get) < 2 do
      if (← IO.monoMsNow) > deadline then throw (IO.userError "pool-backlog setup timed out")
      IO.sleep 1
  let ((samples, settle, inputOK, finalMissing), final) ← (show M _ from do
    let mut samples := "frame,phase,step_us,missing_pixels,offset,mounted\n"
    let mut inputOK := true
    let mut pos := 0
    for i in [0:180] do
      -- Three reversals. New viewport demand arrives before old pictures
      -- can all finish; no pause lets abandoned work drain between legs.
      let delta : Int := if i < 60 then 500 else if i < 100 then -650 else if i < 145 then 700 else -450
      pos := (Int.ofNat pos + delta).toNat
      let limit := (← sm.maxB.get).toUInt64.toNat
      pos := min pos limit
      sm.b.set pos.toFloat
      let text := s!"typing through scroll {i}"
      sm.native.set text
      let t0 ← IO.monoNanosNow
      discard <| App.step [.text]
      let us := ((← IO.monoNanosNow) - t0) / 1000
      let s ← get
      inputOK := inputOK && s.text == text && (← sm.native.get) == text
      samples := samples ++ s!"{i},fling,{us},{missing s},{s.b},{s.rows.size}\n"
      if us < 16000 then IO.sleep ((16000 - us) / 1000).toUInt32
    let stop ← IO.monoMsNow
    release.set true
    let mut settled := none
    for i in [0:400] do
      let t0 ← IO.monoNanosNow
      discard <| App.step []
      let us := ((← IO.monoNanosNow) - t0) / 1000
      let s ← get
      samples := samples ++ s!"{180+i},stop,{us},{missing s},{s.b},{s.rows.size}\n"
      if missing s == 0 then settled := some ((← IO.monoMsNow) - stop); break
      IO.sleep 5
    let s ← get
    writePpm (dir ++ "/stopped.ppm") s.W (← screenOf sm s.W s.Hs s.insetBot)
    return (samples, settled, inputOK, missing s)).run initial
  IO.FS.writeFile (dir ++ "/frames.csv") samples
  release.set true
  for task in blockers do discard <| IO.wait task
  IO.println s!"scrolling: typing={inputOK} settle_ms={settle} missing_pixels={finalMissing} rows={final.rows.size}"
  if let some worker := final.reader then discard <| worker.stop
  return if inputOK && settle.isSome && finalMissing == 0 then 0 else 1

end Scrolling

def main (args : List String) : IO Unit := do
  let code ← try Scrolling.run (args.headD "out/scrolling") (args[1]? == some "backlog")
    catch e => IO.eprintln s!"scrolling: {e}"; pure 1
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
