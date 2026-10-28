/-
A photo arriving chunk by chunk, on the app's own session without a
window (the same `App.step` the phone runs):

1. founds a community and opens its conversation;
2. makes a message with one photo by the engine's send intent, and
   delivers its post and attachment as sync would, without its chunks;
3. delivers the chunks one at a time, out of order; after each, the
   mounted row's picture counts it (got k of n, `Community.progress`),
   its pill reads ⌊100k/n⌋% of the file's size, the ring in the row's
   painted pixels is exactly `Arrival.lit` for (k, n) and lights more
   with each chunk, the softened preview is what shows, and the row's
   height never changes;
4. delivers one chunk twice: nothing changes;
5. delivers the last chunk: the pill is gone and the file, pixel for
   pixel its own decode, replaces the preview;
6. sends a photo from this device with the writer paused: its chunks
   are only in the outbox, and the file shows, not a placeholder.

    arrival <outdir>
-/
import Quiet
import QTests.Sim

open App Engine Community Data

def rowOf (x : Id) : M (Option RowSt) := do return (← get).rows[x]?

/-- Step until row x's paint is current (or give up). -/
def settle (x : Id) : M Unit := do
  for _ in [0:400] do
    let _ ← step []
    match (← get).rows[x]? with
    | some r => if r.task.isNone && r.painted.1 == r.ver && r.shown.isSome then return
    | none => pure ()
    IO.sleep 2

/-- Step until picture p shows its file (or give up): what it shows. -/
def awaitFile (x : Id) : M (Option Paint.Bitmap × Bool) := do
  let mut last := (none, false)
  for _ in [0:2000] do
    let _ ← step []
    if let some r := (← get).rows[x]? then
      if let (some p, some bx) := (r.data.pics[0]?, r.lay.pics[0]?) then
        last ← image p bx.w bx.h
        if last.2 then return last
    IO.sleep 2
  return last

def sameRows (a b : Paint.Bitmap) : Bool := a.w == b.w && a.rows == b.rows

/-- The ring's pixels in a painted row: whether each pixel on the ring is
the arc's colour exactly where `Arrival.lit` says and the track's
elsewhere, and how many are lit. -/
def ringPixels (dm : Row.Dim) (bmp : Paint.Bitmap) (pl : Arrival.Pill) : Bool × Nat := Id.run do
  let z := dm.arrival
  let mut ok := true
  let mut n := 0
  for j in [0:2 * z.ring] do
    let row := bmp.rows[pl.ry + j]!
    for i in [0:2 * z.ring] do
      if Arrival.onRing z.ring z.stroke i j then
        let lit := Arrival.lit z.ring z.stroke pl.got pl.total i j
        if lit then n := n + 1
        if Paint.getPx row (pl.rx + i) != (if lit then z.ink else z.track) then ok := false
  return (ok, n)

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/arrival"
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
  let sm ← Sim.new
  let W := 1080
  let Hs := 2400
  let s ← App.start sm.io #[1080, 2400, 128, 63, 420] (dir ++ "/quiet.db")
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    if !ok then fails.modify (· + 1)
    (← IO.getStdout).flush
  let ((), _) ← (show M Unit from do
    steps 3
    sm.cmds.modify (·.push "found general")
    steps 5
    let s ← get
    if let some pg := s.pageNow then
      if let some (b, _) := pg.taps.find? (·.2 == .openChannel 0) then
        sm.cmds.modify (·.push s!"page {b.x + b.w / 2} {b.y + b.h / 2}")
    steps 3
    check "the conversation is open" ((← get).page == .chat)
    -- sizes as libquiet's humanBytes words them (its JS, run on these)
    let js : List (Nat × String) := [(0, "0 B"), (1023, "1023 B"), (1024, "1.0 KiB"), (1075, "1.0 KiB"),
      (1076, "1.1 KiB"), (10188, "9.9 KiB"), (10189, "10.0 KiB"), (10239, "10.0 KiB"), (10240, "10 KiB"),
      (10751, "10 KiB"), (10752, "11 KiB"), (674944, "659 KiB"), (1048575, "1024 KiB"), (1048576, "1.0 MiB"),
      (2097152, "2.0 MiB"), (3198156, "3.0 MiB"), (3198157, "3.1 MiB"), (10485759, "10.0 MiB"),
      (10485760, "10 MiB"), (5368709120, "5.0 GiB"), (1099511627776, "1024 GiB")]
    let bad := js.filter fun (n, w) => Arrival.humanBytes n != w
    check s!"sizes are worded as libquiet's humanBytes words them ({js.length} sizes; differing {bad})" bad.isEmpty
    -- a message with one photo, its ops as the send intent makes them
    let s ← get
    let bytes ← IO.FS.readBinFile "assets/0.qoi"
    let some src := Image.decode bytes | check "the photo decodes" false
    let (k?, _) ← readView (Community.currentKey s.me.c) #[]
    let some k := k? | check "the community has a content key" false
    let file : NewFile := { info := { name := "photo.qoi".toUTF8, kind := "image/qoi".toUTF8, w := src.w,
                                      h := src.h, preview := Chaos.preview bytes },
                            bytes, key := ← Engine.Crypto.randomBytes 32, nonce := ← Engine.Crypto.randomBytes 24,
                            metaNonce := ← Engine.Crypto.randomBytes 24 }
    let w := Community.send s.me.c s.me.adm s.me.seed k (← Engine.Crypto.randomBytes 24)
      "A photo, arriving".toUTF8 (newestTime s + 1) [file]
    let post :: att :: chunks := w.ops | check "the send makes a post, an attachment and chunks" false
    let n := chunks.length
    let len := (fileCipher file).size
    check s!"the file is {n} chunks ({Arrival.humanBytes len})" (n ≥ 4 && n == Merkle.nChunks len)
    s.wr.submit ⟨[post, att], false⟩
    waitIdle sm
    let x := post.id
    settle x
    check "the post is the newest row" ((← get).ids[0]?.map (·.2) == some x)
    let some r0 ← rowOf x | check "the row is mounted" false
    let h0 := r0.lay.h
    let dm := (← get).dim
    let font := (← get).font
    -- the preview as it should show: decoded at the box's size, softened
    let some bx := r0.lay.pics[0]? | check "the row has a picture" false
    let some psrc := Image.decode file.info.preview | check "the preview decodes" false
    let wantPre := Arrival.soften Row.bg (Image.scaled psrc bx.w bx.h Row.bg)
    let need (t : String) := dm.arrival.fixed + Paint.Line.width font (Text.oneLine font bx.w t)
    IO.println s!"picture box {bx.w}x{bx.h} px; the pill needs {2 * dm.arrival.inset + dm.arrival.height font} px of height, and of width {need "99%"} px with the percent alone, {need s!"99% of {Arrival.humanBytes len}"} px with the caption"
    -- deliver the chunks one at a time: the even indices, then the odd, descending
    let order := ((List.range n).filter (· % 2 == 0)).reverse ++ ((List.range n).filter (· % 2 == 1)).reverse
    let mut lits : Array Nat := #[]
    let mut stepsOk := true
    for kk in [0:n + 1] do
      if kk > 0 then
        s.wr.submit ⟨[chunks[order[kk - 1]!]!], false⟩
        waitIdle sm
        settle x
      let some r ← rowOf x | do stepsOk := false; continue
      let some p := r.data.pics[0]? | do stepsOk := false; continue
      let pl := Row.arrival font dm bx p
      let (img, isFile) ← image p bx.w bx.h
      if kk < n then
        let words := s!"{100 * kk / n}% of {Arrival.humanBytes len}"
        let (ringOk, lit) := match r.shown, pl with
          | some bmp, some pl => ringPixels dm bmp pl
          | _, _ => (false, 0)
        lits := lits.push lit
        let ok := p.got == kk && p.total == n && !p.complete && (pl.map (·.words)) == some words &&
          !isFile && (img.map (sameRows · wantPre)).getD false && ringOk && r.lay.h == h0
        IO.println s!"{if ok then "ok  " else "FAIL"} chunk {kk} of {n}: got {p.got}/{p.total}, pill {(pl.map (·.words))}, ring {lit} px lit{if ringOk then "" else " (pixels differ from Arrival.lit)"}, preview shown {!isFile}, height {r.lay.h}"
        if !ok then stepsOk := false
        if kk == n / 2 then writePpm (dir ++ "/arriving.ppm") W (← screenOf sm W Hs 63)
        -- a chunk delivered twice changes nothing
        if kk == 2 then
          let ver := r.ver
          s.wr.submit ⟨[chunks[order[0]!]!], false⟩
          waitIdle sm
          settle x
          let some r' ← rowOf x | do stepsOk := false; continue
          check s!"a chunk delivered twice changes nothing (got {(r'.data.pics[0]?.map (·.got))}, version {r'.ver})"
            (r'.ver == ver && r'.data == r.data)
      else
        check s!"all {n} chunks: complete, the pill gone" (p.got == n && p.complete && pl.isNone && r.lay.h == h0)
    check "each chunk step shows its count, words, ring and the preview" stepsOk
    check s!"the ring lights more with each chunk, from none ({lits.toList})"
      (lits[0]? == some 0 && (List.range (lits.size - 1)).all fun i => lits[i]! ≤ lits[i + 1]!)
    check "the ring lights strictly more over the download" ((lits[0]?.getD 0) < (lits.back?.getD 0))
    let (img, isFile) ← awaitFile x
    let wantFile := Image.scaled src bx.w bx.h Row.bg
    check "the file replaces the preview, pixel for pixel its own decode"
      (isFile && (img.map (sameRows · wantFile)).getD false)
    settle x
    writePpm (dir ++ "/arrived.ppm") W (← screenOf sm W Hs 63)
    -- sending: the writer paused, the chunks only in the outbox
    let tapComposer (h : Composer.Hit) : M Unit := do
      let s ← get
      let l := composerLayout s
      let box := match h with
        | .send => some l.send
        | h => (l.deck.find? (fun (p : Composer.Box × Composer.Hit) => p.2 == h)).map (fun (p : Composer.Box × Composer.Hit) => p.1)
      if let some b := box then
        onTap .composer (b.x + b.w / 2) (b.y + b.h / 2) false
        steps 2
    tapComposer .addPhotos
    let some (sent, _, _, _) := (← get).chips[0]? | check "a photo attaches" false
    let some ssrc := Image.decode sent | check "the attached photo decodes" false
    sm.cmds.modify (·.push "pause")
    steps 1
    tapComposer .send
    steps 3
    let some (_, y) := (← get).ids[0]? | check "the sent message is listed" false
    let some ry ← rowOf y | check "the sent message is mounted" false
    let some sbx := ry.lay.pics[0]? | check "the sent message has a picture" false
    let some sp := ry.data.pics[0]? | check "the sent message has a picture" false
    check s!"sent, pending: complete from the outbox ({sp.got}/{sp.total}), no pill"
      (ry.data.pending && sp.complete && (Row.arrival font dm sbx sp).isNone)
    let (simg, sfile) ← awaitFile y
    check "the sender sees the file, its own decode, while its chunks are only in the outbox"
      (sfile && (simg.map (sameRows · (Image.scaled ssrc sbx.w sbx.h Row.bg))).getD false &&
        ((← rowOf y).map (·.data.pending)).getD false)
    sm.cmds.modify (·.push "resume")
    waitIdle sm
    let (n1, n2) := ((← get).ids.size, (← get).total)
    check s!"then stored ({n1} listed of {n2})" (((← rowOf y).map (!·.data.pending)).getD false)
    pure ()).run s
  (← IO.getStdout).flush
  -- the writer's task would keep the process alive
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
