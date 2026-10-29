/- A mounted attachment keeps its chunk query until bytes arrive.
Hold the real reader back for three frames after the first miss, then
release it: decoding must begin promptly, with no polling/retry timer.
Negative controls remove the declaration or ignore its available answer.
    pic_retry <outdir>
-/
import Quiet
import platforms.headless.Sim

open App Engine Community Data

def fresh (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)

/-- Whether this picture's file decode has started (its chunks were had). -/
def fileStarted (s : St) (p : Row.Pic) : Bool :=
  s.imgs.toList.any fun (k, _) => k.1 == p.hash.push 1

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/pic_retry"
  fresh dir
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let sm ← Sim.new
  let s0 ← App.start sm.io #[1080, 2400, 128, 63, 420] (dir ++ "/quiet.db")
  let ((), _) ← (show M Unit from do
    sm.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sm
    sm.cmds.modify (·.push "channel")
    steps 2
    sm.cmds.modify (·.push "photo")
    steps 2
    sm.cmds.modify (·.push "post a photo")
    -- frame by frame, until the post's picture has been drawn once
    -- without its chunks: its first miss, a retry filed
    let mut miss := false
    for _ in [0:400] do
      steps 1
      if !(← get).imgWaiting.isEmpty then miss := true; break
      IO.sleep 1
    let s ← get
    let some p := (s.rows.toList.find? (·.2.data.text == "a photo")) >>= fun (_, r) => r.data.pics.head?
      | check "the post's picture is on screen" false
    check s!"the picture declares its first attachment read before decoding ({p.got}/{p.total})"
      (miss && !fileStarted s p)
    -- the reader held back three frames (a reader thread mid-pass)
    let r := s.rst
    modify fun s => { s with rst := none }
    steps 3
    check "no decode starts while the reader is held back" (!fileStarted (← get) p)
    let f0 := (← get).frames
    modify fun s => { s with rst := r }
    let mut started := none
    for i in [0:60] do
      steps 1
      if fileStarted (← get) p then started := some (i + 1); break
    check s!"its file's decode starts within a few frames of the reader's pass ({started}, not 120)"
      (match started with | some n => n ≤ 5 | none => false)
    check s!"before its retry falls due (frame {(← get).frames - f0} of 120)" ((← get).frames - f0 < 120)
    ).run s0
  let n ← fails.get
  IO.println s!"pic_retry: {if n == 0 then "all passed" else s!"{n} failed"}"
  -- the writer's thread would keep the process up: exit, as the others do
  (← IO.getStdout).flush
  IO.Process.exit (if n == 0 then 0 else 1)
