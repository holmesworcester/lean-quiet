/-
The app without a window: the same `App.step` the phone runs, on an `Io`
made of refs. A scripted session on a fresh database:

1. founds the community, then makes chaos (500 messages unless given);
2. waits for the writer, pinned to the newest message, and checks the
   screen shows the newest rows, painted;
3. flings to the top and back at a phone's top speed (about 100 rows a
   second), measuring the app's time per frame and counting viewport
   rows left unpainted;
4. sends a message and reacts, checking each shows at once (pending)
   and then as stored, under the same id;
5. writes screenshots (the list placed at the offset, with the header
   and composer) as PPM.

    host <messages> <outdir>
-/
import Quiet
import Tests.Lib

open App Engine Community Data

structure Sim where
  b : IO.Ref Float
  replies : IO.Ref (Array String)
  cmds : IO.Ref (Array String)
  last : IO.Ref (Array ByteArray × Nat × Nat × Array ByteArray × Array ByteArray)
  maxB : IO.Ref Float

def Sim.new : IO Sim := do
  return ⟨← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef (#[], 0, 0, #[], #[]), ← IO.mkRef 0⟩

def Sim.io (sm : Sim) : Io where
  screen := pure #[1080, 2400, 128, 63, 420]
  scroll ch vh := do
    let mx := if ch > vh then (ch - vh).toNat.toFloat else 0
    sm.maxB.set mx
    let b ← sm.b.get
    let b := if b < 0 then 0 else if b > mx then mx else b
    sm.b.set b
    return b.toUInt32
  scrollBy d := sm.b.modify (· + d)
  scrollTo b := sm.b.set b
  frame fr b o top bot := do sm.last.set (fr, b.toNat, o.toNat, top, bot); return #[]
  text := pure ("", #[0, 0, 0, 0])
  ime _ := pure ()
  textClear := pure ()
  copy t := sm.replies.modify (·.push s!"copied {t}")
  ctlPoll := sm.cmds.modifyGet fun c => (c, #[])
  ctlReply s := sm.replies.modify (·.push s)
  nowUs := do return (← IO.monoNanosNow).toUInt64 / 1000

/-- The screen as the twin composes it: header, the list's viewport rows,
the composer above the bottom inset. -/
def screenOf (sm : Sim) (W Hs insetBot : Nat) : IO (Array ByteArray) := do
  let (fr, _, o, top, bot) ← sm.last.get
  let bg := Paint.solid Row.bg W
  let mut out := Array.replicate Hs bg
  for i in [0:top.size] do out := out.set! i top[i]!
  let vh := Hs - top.size - bot.size - insetBot
  for r in [0:vh] do
    if let some row := fr[o + r]? then out := out.set! (top.size + r) row
  for i in [0:bot.size] do out := out.set! (top.size + vh + i) bot[i]!
  return out

def writePpm (path : String) (W : Nat) (rows : Array ByteArray) : IO Unit := do
  let mut b := s!"P6\n{W} {rows.size}\n255\n".toUTF8
  for r in rows do
    for i in [0:W] do
      b := b.push r[4*i]! |>.push r[4*i+1]! |>.push r[4*i+2]!
  IO.FS.writeBinFile path b

/-- Viewport rows that show no painted row although content is there. -/
def blanks (s : St) (sm : Sim) : IO Nat := do
  let (fr, b, o, _, _) ← sm.last.get
  let vh := viewH s
  let (bots, _) := bottoms s
  let mut n := 0
  for r in [0:vh] do
    let p := b + vh - 1 - r
    -- content at p?
    let mut inRow := false
    for i in [0:s.ids.size] do
      let bot := bots[i]!
      if bot ≤ p && p < bot + heightOf s s.ids[i]!.2 then inRow := true; break
      if bot > p then break
    if inRow && (fr[o + r]?.map (· == s.bgRow) |>.getD true) then
      -- a painted row's background rows are the shared row too: count
      -- only rows of rows not yet painted
      match rowAt s p with
      | some (x, _) => if (s.rows[x]? >>= (·.shown)).isNone then n := n + 1
      | none => pure ()
  return n

/-- Every answer the live cache holds as fresh equals the query run now:
no notice was missed and no watch is too narrow. Counts the answers
checked and the stale ones found fresh. -/
def liveSound : M (Nat × Nat) := do
  let s ← get
  -- take what the writer has filed first: a fresh answer is promised only
  -- up to the notices the frame has seen
  let ns ← s.wr.takeNotices
  modify fun s => { s with live := s.live.notice ns }
  let s ← get
  let mut n := 0
  let mut bad := 0
  for (q, e) in s.live.entries.toList do
    if e.stale then continue
    let now ← q.run s.rd s.out
    n := n + 1
    if now != e.ans then
      bad := bad + 1
      if bad ≤ 5 then
        let desc := match q, e.ans, now with
          | .list lq, .list a pa, .list b pb =>
            s!"list key {Tests.hex lq.key}… limit {lq.limit} desc {lq.desc}: held {a.rows.length}/{a.inRange}/{a.total} pend {pa.length}, now {b.rows.length}/{b.inRange}/{b.total} pend {pb.length}"
          | .bytes .., _, _ => "bytes"
          | _, _, _ => "other"
        IO.eprintln s!"stale fresh answer: {desc}"
  return (n, bad)

def steps (n : Nat) : M Unit := do
  for _ in [0:n] do
    let _ ← step []

def waitIdle (sm : Sim) : M Unit := do
  -- wait for a new idle reply: earlier ones are still in the replies
  let before := ((← sm.replies.get).filter (·.startsWith "idle")).size
  sm.cmds.modify (·.push "wait")
  let mut k := 0
  while ((← sm.replies.get).filter (·.startsWith "idle")).size == before && k < 20000 do
    let _ ← step []
    IO.sleep 1
    k := k + 1
  -- let paints finish
  for _ in [0:30] do
    let _ ← step []
    IO.sleep 2

def main (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 500
  let dir := args[1]?.getD "out/host"
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
  let ((), s) ← (show M Unit from do
    steps 3
    check "a new install opens on Get started" ((← get).page == .getStarted)
    writePpm (dir ++ "/get-started.ppm") W (← screenOf sm W Hs 63)
    sm.cmds.modify (·.push "found general")
    steps 5
    check "founding a community opens its conversation" ((← get).page == .chat && (← get).me.name == "general")
    sm.cmds.modify (·.push s!"chaos {n}")
    let t0 ← IO.monoMsNow
    waitIdle sm
    let t1 ← IO.monoMsNow
    IO.println s!"chaos {n}: written and settled in {t1 - t0} ms"
    let s ← get
    check s!"all {n} messages listed" (s.total == n)
    check "people counted" (s.people > 6)
    let ppl := s.people
    IO.println s!"people {ppl}, loaded ids {s.ids.size}, mounted rows {s.rows.size}"
    writePpm (dir ++ "/bottom.ppm") W (← screenOf sm W Hs 63)
    check "bottom screen painted" ((← blanks s sm) == 0)
    let (n1, b1) ← liveSound
    check s!"after chaos, every fresh live answer equals the query now ({n1} answers)" (b1 == 0 && n1 > 0)
    if args[2]? == some "seed" then
      (← IO.getStdout).flush
      IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
    -- a cold open: a new state on the same database
    pure ()).run s
  -- pages, a second community, switching, and a joiner approved
  let ((), s) ← (show M Unit from do
    sm.cmds.modify (·.push "open switcher")
    steps 3
    writePpm (dir ++ "/switcher.ppm") W (← screenOf sm W Hs 63)
    -- Add a community → Get started → Create a new community, by taps on
    -- the pages' own boxes
    let tapAct (a : Pages.Act) : M Bool := do
      let s ← get
      let some pg := s.pageNow | return false
      match pg.taps.find? (·.2 == a) with
      | some (b, _) =>
        sm.cmds.modify (·.push s!"page {b.x + b.w / 2} {b.y + b.h / 2}")
        steps 3
        return true
      | none => return false
    check "the switcher offers Add a community" (← tapAct .addCommunity)
    check "Get started offers Create a new community" (← tapAct .createCommunity)
    check "Create shows its name field" ((← get).page == .create)
    modify fun s => { s with field := "design team" }
    steps 2
    writePpm (dir ++ "/create.ppm") W (← screenOf sm W Hs 63)
    check "Continue founds it" (← tapAct .continue_)
    waitIdle sm
    let s ← get
    check s!"two communities, the new one current: {s.comms.map (·.name)}" (s.comms.size == 2 && s.me.name == "design team" && s.total == 0)
    sm.cmds.modify (·.push "switch 0")
    steps 5
    check s!"switching back shows the first community's {(← get).total} messages" ((← get).me.name == "general" && (← get).total > 0)
    -- a joiner: invited by me, asking with its own device and the link's bearer
    let s ← get
    let joiner := Device.named "joiner-test"
    let bearer := Device.named "joiner-bearer"
    let inv := Community.invite s.me.c s.me.adm s.me.dev bearer.pk false 1
    let rq := Community.request s.me.c inv.id joiner bearer.sk
    s.wr.submit ⟨[inv, rq], [], false⟩
    waitIdle sm
    steps 3
    check s!"the joiner waits under join requests ({(← get).asking.size})" ((← get).asking.size == 1)
    sm.cmds.modify (·.push "open requests")
    steps 3
    writePpm (dir ++ "/requests.ppm") W (← screenOf sm W Hs 63)
    check "its approve button approves" (← tapAct (.approve 0))
    waitIdle sm
    steps 5
    waitIdle sm
    steps 5
    let s ← get
    let admitted : Bool ← match ← read (.list (Community.admission.byDevice.query [s.me.c, joiner.pk] (limit := some 0))) with
      | .list a _ => pure (decide (a.total > 0))
      | _ => pure false
    check "the approval completes the tally and the joiner is admitted" (admitted && (← get).asking.isEmpty)
    for (pg, name) in [("join", "join"), ("openInvite", "open-invite"), ("paste", "paste"), ("scan", "scan"),
        ("agree", "agree"), ("waiting", "waiting"), ("invite", "invite")] do
      sm.cmds.modify (·.push s!"open {pg}")
      steps 3
      writePpm (dir ++ s!"/{name}.ppm") W (← screenOf sm W Hs 63)
      sm.cmds.modify (·.push "back")
      steps 2
    pure ()).run s
  -- cold open timing
  let t0 ← IO.monoMsNow
  let s2 ← App.start sm.io #[1080, 2400, 128, 63, 420] (dir ++ "/quiet.db")
  sm.b.set 0
  let ((), s2) ← (show M Unit from do
    let mut k := 0
    repeat
      let _ ← step []
      k := k + 1
      if (← blanks (← get) sm) == 0 && (← get).total == n || k > 2000 then break
      IO.sleep 1
    let t1 ← IO.monoMsNow
    IO.println s!"cold open: first fully painted screen after {t1 - t0} ms ({k} frames)"
    writePpm (dir ++ "/open.ppm") W (← screenOf sm W Hs 63)
    -- a fling to the top: 100 rows a second at 60 fps is ~250 px a frame
    let mut worst := 0
    let mut blankFrames := 0
    let mut frames := 0
    let tf0 ← IO.monoMsNow
    let mut times := #[]
    repeat
      let mx ← sm.maxB.get
      let b ← sm.b.get
      if b ≥ mx then break
      sm.b.set (b + 250)
      let ta ← IO.monoNanosNow
      let _ ← step []
      let tb ← IO.monoNanosNow
      times := times.push ((tb - ta) / 1000)
      IO.sleep 16
      let bl ← blanks (← get) sm
      if bl > 0 then blankFrames := blankFrames + 1
      worst := max worst bl
      frames := frames + 1
      if frames == 40 then writePpm (dir ++ "/fling.ppm") W (← screenOf sm W Hs 63)
      if frames > 5000 then break
    let tf1 ← IO.monoMsNow
    let sorted := times.qsort (· < ·)
    IO.println s!"fling to top: {frames} frames in {tf1 - tf0} ms; step µs median {sorted[sorted.size/2]?.getD 0} p95 {sorted[sorted.size*95/100]?.getD 0} max {sorted.back?.getD 0}; frames with unpainted rows {blankFrames}, worst {worst} rows"
    steps 30
    writePpm (dir ++ "/top.ppm") W (← screenOf sm W Hs 63)
    let s ← get
    IO.println s!"at the top: loaded {s.ids.size} of {s.total}, mounted {s.rows.size}"
    -- back to the newest; send and react
    sm.b.set 0
    steps 10
    sm.cmds.modify (·.push "pause")
    sm.cmds.modify (·.push "send Hello from the host test 👋 שלום")
    let _ ← step []
    let s ← get
    let top : Option Id := s.ids[0]?.map (fun (p : Pos) => p.2)
    let pend := match top with
      | some x => (s.rows[x]?.map (fun (r : RowSt) => r.data.pending)).getD false
      | none => false
    let mut j := 0
    while ((← get).rows[(← get).ids[0]!.2]?).isNone && j < 10 do
      let _ ← step []; j := j + 1
    let s ← get
    let p0 := (s.rows[s.ids[0]!.2]?.map (·.data)).map (fun d => (d.text, d.pending))
    check s!"a send shows at once, pending: {p0}" ((p0.map (·.2)).getD false || pend)
    steps 5
    writePpm (dir ++ "/pending.ppm") W (← screenOf sm W Hs 63)
    sm.cmds.modify (·.push "resume")
    waitIdle sm
    let s ← get
    let p1 := (s.rows[s.ids[0]!.2]?.map (·.data)).map (fun d => (d.text, d.pending))
    check s!"then stored, same id: {p1}" (p1.map (·.2) == some false && s.ids[0]!.2 == top.getD .empty)
    let (n2, b2) ← liveSound
    check s!"after a send, every fresh live answer equals the query now ({n2} answers)" (b2 == 0 && n2 > 0)
    sm.cmds.modify (·.push "react 0 🎉")
    let _ ← step []
    steps 3
    let s ← get
    let t := (s.rows[s.ids[0]!.2]?.map (·.data.tallies)).getD []
    check "a reaction shows at once, mine" (t.any fun t => t.emoji == "🎉" && t.mine)
    waitIdle sm
    writePpm (dir ++ "/sent.ppm") W (← screenOf sm W Hs 63)
    -- the reaction sheet on a message, the rest dimmed
    sm.cmds.modify (·.push "tray 1")
    for _ in [0:20] do
      let _ ← step []
      IO.sleep 3
    writePpm (dir ++ "/sheet.ppm") W (← screenOf sm W Hs 63)
    let s ← get
    let m1 := s.ids[1]!.2
    check "the sheet is open, the other rows dimmed" (s.sheet.isSome &&
      (s.rows.fold (fun n x r => if some x != s.selected && r.dimShown.isSome then n + 1 else n) 0) > 0)
    -- tap the quick key for 🎉 at its drawn box's centre
    let q := Sheet.quick s.dim s.W
    let gi := 3
    let kx := q.keys.left gi + q.keys.key / 2
    let ky := q.keys.y0 + q.keys.key / 2
    sm.cmds.modify (·.push s!"sheet tap {kx} {ky}")
    steps 3
    let s ← get
    let t1 := (s.rows[m1]?.map (·.data.tallies)).getD []
    check s!"the quick key under the finger reacts ({Row.quick[gi]!}) and the sheet closes"
      (s.sheet.isNone && t1.any fun t => t.emoji == Row.quick[gi]! && t.mine)
    -- open again, browse, drag the grid, pick the emoji drawn under a cell
    sm.cmds.modify (·.push "tray 1")
    steps 3
    let s ← get
    let bx := q.keys.left 6 + q.keys.key / 2
    sm.cmds.modify (·.push s!"sheet tap {bx} {ky}")
    steps 5
    let s ← get
    check "Browse opens the catalogue" ((s.sheet.map (·.catalog)).getD false)
    writePpm (dir ++ "/catalog.ppm") W (← screenOf sm W Hs 63)
    let sh := s.sheet.get!
    let c := catOf s sh
    let gx := c.grid.x0 + c.grid.key / 2
    let gy := c.grid.y0 + c.grid.vh - c.grid.key / 2
    sm.cmds.modify (·.push s!"sheet drag 0 {gx} {gy}")
    for d in [1:11] do sm.cmds.modify (·.push s!"sheet drag 1 {gx} {gy - d * 60}")
    sm.cmds.modify (·.push s!"sheet drag 2 {gx} {gy - 600}")
    steps 40
    let s ← get
    let sh := s.sheet.get!
    check s!"a drag scrolls the grid (scroll {sh.scroll}, within {c.grid.maxScroll})"
      (sh.scroll > 0 && sh.scroll ≤ c.grid.maxScroll)
    writePpm (dir ++ "/catalog-scrolled.ppm") W (← screenOf sm W Hs 63)
    let c := catOf s sh
    let tx := c.grid.x0 + 2 * c.grid.pitch + c.grid.key / 2
    let ty := c.grid.y0 + c.grid.key
    let picked := c.grid.hit sh.scroll tx ty
    let want := picked.bind fun i => (sheetItems s sh)[i]? >>= (s.catalog[·]?) |>.map (·.e)
    sm.cmds.modify (·.push s!"sheet tap {tx} {ty}")
    steps 3
    let s ← get
    let t2 := (s.rows[m1]?.map (·.data.tallies)).getD []
    check s!"the catalogue cell under the finger reacts with its emoji ({want})"
      (want.isSome && t2.any fun t => some t.emoji == want && t.mine)
    waitIdle sm
    let (n3, b3) ← liveSound
    check s!"after reactions, every fresh live answer equals the query now ({n3} answers)" (b3 == 0 && n3 > 0)
    -- a second chaos lands while the screen is live: every answer still sound
    sm.cmds.modify (·.push "chaos 200")
    waitIdle sm
    let (n4, b4) ← liveSound
    check s!"after more chaos, every fresh live answer equals the query now ({n4} answers)" (b4 == 0 && n4 > 0)
    IO.println (App.stats (← get))
    pure ()).run s2
  let _ := s2
  (← IO.getStdout).flush
  -- the writer's task would keep the process alive
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
