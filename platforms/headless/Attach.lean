/-
Photos over real TCP: two apps, each its own database and its own node
(the engine's Runner with the Connection family, as the phones run it),
joined on loopback as host:net-join joins them, then one photo each way.

Everything is driven over ctl, as the demo drives the phones: the join
(`link`, `open paste`, `field`, `act continue|agree|approve`) and each
photo, attached as the composer's Add photos attaches it (`photo`: a
bundled test photo, prepared as QOI) and sent (`post`: the post, its
attachment, and the file's chunks: 64 KiB slices
of the ciphertext, each with its Merkle path, so one chunk op is larger
than a frame bundle's 48 KiB and goes out as a frame of its own). The
other app must end with the post's picture complete (every chunk, as
chunk.byFile counts them), the file opened from its chunks equal to the
bytes sent, and its row drawn from the file, not the preview.

    attach <outdir>
-/
import Quiet
import platforms.headless.Sim

open App Engine Community Data

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

/-- Attach the next test photo and post it with text t, over ctl as on a
phone (`photo`, `post`): the bytes sent. -/
def post (sm : Sim) (t : String) : M ByteArray := do
  sm.cmds.modify (·.push "channel")
  steps 2
  sm.cmds.modify (·.push "photo")
  steps 2
  let bytes := ((← get).chips[0]?.map (·.1)).getD .empty
  sm.cmds.modify (·.push s!"post {t}")
  steps 3
  return bytes

/-- On this app: the post's picture once complete, the file opened from its
chunks, and whether its row draws the file (polled until it does). -/
def received (sm : Sim) (t : String) : M (Option (Row.Pic × Option ByteArray × Bool × Nat)) := do
  sm.cmds.modify (·.push "channel")
  steps 2
  let some p := picOf (← get) t | return none
  -- the largest chunk op, as stored (its encoded size)
  let mut big := 0
  for x in p.chunks do
    if let some o ← (Store.getOp (F := SF) (m := SqlM SF) x).run (← get).rd then
      big := max big (Codec.encode o).size
  -- drawn from the file: the file stage, and not the placeholder a failed
  -- open draws
  let mut full := false
  for _ in [0:400] do
    let (b, f) ← image p 96 64
    if f && (b.map (·.rows[0]? != some (Paint.solid Row.placeholder 96))).getD false then full := true; break
    steps 1; IO.sleep 10
  -- the file opened from the chunks stored by now (asked of the reader's
  -- board, as a paint asks: wanted from the next frame)
  let mut raw := none
  for _ in [0:50] do
    raw ← slicesOf p
    if raw.isSome then break
    steps 1
  let opened := (raw >>= Pics.slicesFromOps) >>= fun sl => Community.openFile sl p.key p.nonce
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
  let (pa, pb) ← testPorts
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db") (some (pa, true))
  let b0 ← App.start sb.io screen (dir ++ "/b/quiet.db") (some (pb, true))
  -- the join, over ctl as it is driven on the phones: A's `link`; B's
  -- Paste page, `field` (as typed), `act continue` / `act agree`
  let (link, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sa
    steps 3
    sa.cmds.modify (·.push "open invite")
    sa.cmds.modify (·.push "link")
    steps 3
    return (← sa.replies.get).back?.getD "").run a0
  check s!"A's `link` is its invite ({link.take 24}…)" (link.startsWith "quiet://join/")
  let ((), b1) ← (show M Unit from do
    steps 2
    for c in ["open paste", s!"field {link}", "act continue", "field Bea", "act continue", "act agree"] do
      sb.cmds.modify (·.push c)
      steps 3
    waitIdle sb
    steps 3).run b0
  let (a2, b2, asked) ← both a1 b1 20000 fun a _ => a.asking.size == 1
  check "A sees B's request over TCP" asked
  let ((), a3) ← (show M Unit from do
    for c in ["switch club", "open requests", "act approve 0"] do
      sa.cmds.modify (·.push c)
      steps 3).run a2
  let (a4, b4, inB) ← both a3 b2 30000 fun _ b => !b.me.waiting && b.me.name == "club"
  check "B is admitted" inB
  -- one photo each way
  let mut a := a4
  let mut b := b4
  for (fromA, t) in [(true, "a photo from Ann"), (false, "a photo from Bea")] do
    let (sent, s') ← (post (if fromA then sa else sb) t).run (if fromA then a else b)
    if fromA then a := s' else b := s'
    -- the sender's own row: its photo drawn from the file too
    let (mine, s'') ← (received (if fromA then sa else sb) t).run (if fromA then a else b)
    if fromA then a := s'' else b := s''
    match mine with
    | none => check s!"{t}: on the sender's own screen" false
    | some (p, opened, full, _) =>
      check s!"{t}: the sender's own copy opens to the bytes sent ({p.got}/{p.total})" (opened == some sent)
      check s!"{t}: the sender's own row draws the file, not a placeholder" full
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
  -- four photos in one post with no text (Add photos four times and Send,
  -- as the user did on the Pixel), then a text: the sender's outbox
  -- drains, the other side gets every chunk
  let t4 := ""
  let ((), b5) ← (show M Unit from do
    sb.cmds.modify (·.push "channel")
    steps 2
    for _ in [0:4] do
      sb.cmds.modify (·.push "photo")
      steps 2
    sb.cmds.modify (·.push "post")
    steps 3
    sb.cmds.modify (·.push "post and a text after it")
    steps 3).run b
  b := b5
  let (a', b', drained) ← both a b 60000 fun _ y => y.out.isEmpty
  a := a'; b := b'
  check s!"four photos: the sender's outbox drains ({b.out.size} left)" drained
  let pics4 (x : St) := ((x.rows.toList.find? (·.2.data.text == t4)).map (·.2.data.pics)).getD []
  let ((), a5) ← (show M Unit from do sa.cmds.modify (·.push "channel"); steps 2).run a
  a := a5
  let (a', b', got) ← both a b 120000 fun x _ =>
    (pics4 x).length == 4 && (pics4 x).all (·.complete) &&
      x.rows.toList.any (·.2.data.text == "and a text after it")
  a := a'; b := b'
  check s!"four photos: all four complete on the other side ({(pics4 a).map fun p => s!"{p.got}/{p.total}"}), and the text after" got
  -- QUIET_IDLE_MS: both apps keep stepping, idle with their photos on
  -- screen, for a CPU profile (per thread: top -H -p <pid>)
  if let some ms := (← IO.getEnv "QUIET_IDLE_MS") >>= String.toNat? then
    IO.println s!"idle {ms} ms, pid {← IO.Process.getPID}"; (← IO.getStdout).flush
    let (a', b', _) ← both a b ms fun _ _ => false
    let fin (x : St) : IO Nat := x.imgs.toList.foldlM (fun n (_, t) => do return n + (if ← IO.hasFinished t then 1 else 0)) 0
    IO.println s!"idle: finished decodes {← fin a'}/{a'.imgs.size} and {← fin b'}/{b'.imgs.size}"
    IO.println s!"idle: paints {a.paints} → {a'.paints} and {b.paints} → {b'.paints}, imgs {a'.imgs.size} {b'.imgs.size}, frames {a'.frames - a.frames}"
  if let some r := a.net then r.stop
  if let some r := b.net then r.stop
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
