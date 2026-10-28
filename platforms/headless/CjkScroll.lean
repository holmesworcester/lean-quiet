/-
Five hundred CJK-heavy, signed and sealed posts through the actual app.
Fast scrolling measures App.step and missing painted viewport rows; the
same corpus is used before and after enabling CJK. No network is used.
-/
import platforms.headless.Sim

open App Engine Community Data

private def blanks (s : St) : Nat := Id.run do
  let (bots, _) := bottoms s
  let mut n := 0
  for i in [0:s.ids.size] do
    let id := s.ids[i]!.2
    let bot := bots[i]!
    if bot < s.b + viewH s && bot + heightOf s id > s.b then
      if (s.rows[id]? >>= (·.shown)).isNone then n := n + 1
  return n

def main (args : List String) : IO Unit := do
  let dir := args.headD "out/cjk-scroll"
  let corpus := args[1]?.getD "out/cjk/corpus.txt"
  IO.FS.createDirAll dir
  for name in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    let p := dir ++ "/" ++ name
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let messages := ((← IO.FS.readFile corpus).splitOn "\n").filter (!·.isEmpty)
  let sm ← Sim.new
  let s ← App.start sm.io #[1080,2400,128,63,420] (dir ++ "/quiet.db")
  let ((), s) ← (show M Unit from do
    steps 3
    sm.cmds.modify (·.push "found CJK")
    steps 5
    sm.cmds.modify (·.push "channel")
    steps 3
    let s ← get
    let (key?, _) ← readView (Community.currentKey s.me.c) #[]
    let some key := key? | throw (IO.userError "no content key")
    let ops := messages.zipIdx |>.map fun (text, i) =>
      sealedPost s.me.c s.me.adm s.me.dev key (Chaos.bytesOf s!"cjk {i}" 24) text.toUTF8 (i+1) (1000+i)
    s.wr.submit ⟨ops, false⟩
    waitIdle sm
    unless (← get).total == messages.length do throw (IO.userError "CJK messages not listed")
    pure ()).run s
  sm.b.set 0
  let ((), _) ← (show M Unit from do
    let mut times : Array UInt64 := #[]
    let mut missing := 0
    let mut worst := 0
    let mut frames := 0
    for _ in [0:4000] do
      if (← sm.b.get) ≥ (← sm.maxB.get) then break
      sm.b.modify (· + 250)
      let t0 ← IO.monoNanosNow
      let _ ← step []
      times := times.push ((← IO.monoNanosNow) - t0 |>.toUInt64 |>.div 1000)
      IO.sleep 16
      let n := blanks (← get)
      if n > 0 then missing := missing + 1
      worst := max worst n
      frames := frames + 1
      if frames == 40 then writePpm (dir ++ "/fling.ppm") 1080 (← screenOf sm 1080 2400 63)
    steps 30
    writePpm (dir ++ "/top.ppm") 1080 (← screenOf sm 1080 2400 63)
    let sorted := times.qsort (· < ·)
    let p95 := sorted[sorted.size*95/100]?.getD 0
    IO.println s!"CJK scroll: {messages.length} posts; {frames} frames; median {sorted[sorted.size/2]?.getD 0} us; p95 {p95} us; max {sorted.back?.getD 0} us; unpainted frames {missing}, worst {worst} message rows"
    unless frames > 200 && frames < 4000 && blanks (← get) == 0 do
      throw (IO.userError "CJK scroll did not finish with painted content")
    unless p95 < 16667 do throw (IO.userError "CJK scroll exceeds 60 Hz step budget")
    pure ()).run s
  let (hits, misses, bytes, peak, entries) ← Ttf.Memo.stats
  IO.println s!"CJK cache: {hits} hits, {misses} misses, {bytes} charged bytes, peak {peak}, {entries} entries"
  (← IO.getStdout).flush
  IO.Process.exit 0
