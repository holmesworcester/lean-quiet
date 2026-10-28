/-
Photos over real TCP: two apps, each its own database and its own node
(the engine's Runner with the Connection family, as the phones run it),
joined on loopback as host:net-join joins them, then one photo each way.

Each photo is attached as the composer's Add photos attaches it
(`attachPhoto`: a bundled test photo, prepared as QOI) and sent with
`sendNow` (the post, its attachment, and the file's chunks: 64 KiB slices
of the ciphertext, each with its Merkle path, so one chunk op is larger
than a frame bundle's 48 KiB and goes out as a frame of its own). The
other app must end with the post's picture complete (every chunk, as
chunk.byFile counts them), the file opened from its chunks equal to the
bytes sent, and its row drawn from the file, not the preview.

    attach <outdir>
-/
import Quiet
import QTests.Sim

open App Engine Community Data

def tapAct (sm : Sim) (a : Pages.Act) : M Bool := do
  let s ← get
  let some pg := s.pageNow | return false
  match pg.taps.find? (·.2 == a) with
  | some (b, _) =>
    sm.cmds.modify (·.push s!"page {b.x + b.w / 2} {b.y + b.h / 2}")
    steps 3
    return true
  | none => return false

def fresh (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)

/-- Both apps step, in real time, until `p` holds of them (or `ms` pass). -/
def both (a b : St) (ms : Nat) (p : St → St → Bool) : IO (St × St × Bool) := do
  let mut a := a
  let mut b := b
  let t0 ← IO.monoMsNow
  while (← IO.monoMsNow) - t0 < ms do
    if p a b then return (a, b, true)
    a := (← (steps 1).run a).2
    b := (← (steps 1).run b).2
    IO.sleep 5
  return (a, b, p a b)

/-- The picture of the post whose text is `t`, as this app's rows have it. -/
def picOf (s : St) (t : String) : Option Row.Pic :=
  (s.rows.toList.find? (·.2.data.text == t)) >>= fun (_, r) => r.data.pics.head?

/-- Attach the next test photo and post it with text t: the bytes sent. -/
def post (sm : Sim) (t : String) : M ByteArray := do
  sm.cmds.modify (·.push "channel")
  steps 2
  attachPhoto
  let bytes := ((← get).chips[0]?.map (·.1)).getD .empty
  modify fun s => { s with text := t }
  sendNow
  steps 3
  return bytes

/-- On this app: the post's picture once complete, the file opened from its
chunks, and whether its row draws the file (polled until it does). -/
def received (sm : Sim) (t : String) : M (Option (Row.Pic × Option ByteArray × Bool × Nat)) := do
  sm.cmds.modify (·.push "channel")
  steps 2
  let some p := picOf (← get) t | return none
  let opened := Community.openFile (← slicesOf p) p.key p.nonce
  -- the largest chunk op, as stored (its encoded size)
  let mut big := 0
  for x in p.chunks do
    if let some o ← (Store.getOp (F := SF) (m := SqlM SF) x).run (← get).rd then
      big := max big (Codec.encode o).size
  let mut full := false
  for _ in [0:400] do
    let (_, f) ← image p 96 64
    if f then full := true; break
    steps 1; IO.sleep 10
  return some (p, opened, full, big)

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/attach"
  fresh (dir ++ "/a"); fresh (dir ++ "/b")
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let sa ← Sim.new
  let sb ← Sim.new
  let pa := 47221
  let pb := 47222
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db") (some (pa, true))
  let b0 ← App.start sb.io screen (dir ++ "/b/quiet.db") (some (pb, true))
  -- the join, as host:net-join does it
  let (link, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sa
    steps 3
    sa.cmds.modify (·.push "open invite")
    steps 3
    let s ← get
    return ((s.links.find? (·.1 == s.me.acc)).map (·.2)).getD "").run a0
  let ((), b1) ← (show M Unit from do
    steps 2
    let _ ← tapAct sb .joinCommunity
    let _ ← tapAct sb .inviteLink
    let _ ← tapAct sb .pasteLink
    modify fun s => { s with field := link }
    steps 1
    let _ ← tapAct sb .continue_
    modify fun s => { s with field := "Bea" }
    steps 1
    let _ ← tapAct sb .continue_
    let _ ← tapAct sb .agree
    waitIdle sb
    steps 3).run b0
  let (a2, b2, asked) ← both a1 b1 20000 fun a _ => a.asking.size == 1
  check "A sees B's request over TCP" asked
  let ((), a3) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 3
    let _ ← tapAct sa .requests
    let _ ← tapAct sa (.approve 0)
    steps 3).run a2
  let (a4, b4, inB) ← both a3 b2 30000 fun _ b => !b.me.waiting && b.me.name == "club"
  check "B is admitted" inB
  -- one photo each way
  let mut a := a4
  let mut b := b4
  for (fromA, t) in [(true, "a photo from Ann"), (false, "a photo from Bea")] do
    let (sent, s') ← (post (if fromA then sa else sb) t).run (if fromA then a else b)
    if fromA then a := s' else b := s'
    let n := Merkle.nChunks (sent.size + 16)
    check s!"{t}: attached ({sent.size} bytes, {n} chunks of up to {Merkle.sliceSize} bytes)" (sent.size > 0)
    -- the receiver: its conversation open, until the picture is complete
    let r := if fromA then sb else sa
    let ((), r1) ← (show M Unit from do r.cmds.modify (·.push "channel"); steps 2).run (if fromA then b else a)
    if fromA then b := r1 else a := r1
    let (a', b', done) ← both a b 120000 fun x y =>
      ((picOf (if fromA then y else x) t).map (·.complete)).getD false
    a := a'; b := b'
    let rs := if fromA then b else a
    let p := picOf rs t
    check s!"{t}: complete on the other side (chunks {(p.map (·.got)).getD 0}/{(p.map (·.total)).getD 0})" done
    let (got, rs') ← (received r t).run rs
    if fromA then b := rs' else a := rs'
    match got with
    | none => check s!"{t}: on the other side's screen" false
    | some (p, opened, full, big) =>
      let bundle := ({} : Engine.Sync.Config).bundle
      check s!"{t}: a chunk op ({big} bytes) is larger than a frame bundle ({bundle}), and arrived" (big > bundle)
      check s!"{t}: the file opened from its chunks is the bytes sent ({(opened.map (·.size)).getD 0} bytes)"
        (opened == some sent)
      check s!"{t}: its row draws the file, not the preview (chunks {p.got}/{p.total})" full
  if let some r := a.net then r.stop
  if let some r := b.net then r.stop
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
