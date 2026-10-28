/-
The dogfood UX regressions on the app's headless twin. Actual touch
boxes, writer notices, row coordinates, clipboard effects and painted
pages exercise arrivals, full labels, presence, photo reactions, copy,
and switching away from an open sheet. No phones or network required.
-/
import QTests.Sim

open App Engine Community Data

namespace Ux

/-- Touch the control drawn on this page, through App.step. -/
def tap (act : Pages.Act) (long := false) : M Bool := do
  let s ← get
  let some pg := s.pageNow | return false
  let some (b, _) := pg.taps.find? (·.2 == act) | return false
  let e := if long then Event.long else Event.tap
  let _ ← step [e .list (b.x + b.w / 2).toUInt32 (viewH s - 1 - (b.y + b.h / 2)).toUInt32]
  return true

/-- A row's content coordinate relative to the viewport's bottom. -/
def position (s : St) (m : Id) : Option Int :=
  let (bs, _) := bottoms s
  (s.ids.findIdx? (·.2 == m)).map fun i => Int.ofNat bs[i]! - Int.ofNat s.b

end Ux

open Ux

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/ux"
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
  let sm ← Sim.new
  -- The C twin clamps scrollBy immediately; phone shells queue it for
  -- vsync. Exercise both seam behaviours with the same app session.
  let delayed := args[1]? == some "queued"
  let pending ← IO.mkRef (0 : Float)
  let shift (d : Float) : IO Unit := do
    let hi ← sm.maxB.get
    sm.b.modify fun b => max 0 (min hi (b + d))
  let io : Io := { sm.io with
    scrollBy := fun d => if delayed then pending.modify (· + d) else shift d
    frame := fun fr b o top bot pin => do
      if delayed then
        shift (← pending.get)
        pending.set 0
      sm.io.frame fr b o top bot pin }
  let s ← App.start io #[1080, 2400, 128, 63, 420] (dir ++ "/quiet.db")
  let fails ← IO.mkRef 0
  let checks ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    checks.modify (· + 1)
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    if !ok then fails.modify (· + 1)
    (← IO.getStdout).flush
  let ((), _) ← (show M Unit from do
    let longName := "Quiet שלום 👩🏽‍💻 é 社区 full community name"
    sm.cmds.modify (·.push s!"found {longName}|A very long member name that needs its full profile label")
    steps 4; waitIdle sm; steps 3
    let first := (← get).me.acc
    check "long community name is stored without truncation" ((← get).me.name == longName)
    -- The compact header really is truncated, and its long press opens
    -- the full source (including emoji sequences and combining marks).
    let s ← get
    check "fixture exceeds the compact header" ((Text.oneLine s.font (s.W - s.dim.px 140) longName).any (·.c == 0x2026))
    let _ ← step [.long .header 200 160]
    check "long press on the header opens its complete label" ((← get).page == .label && (← get).labelText == longName)
    -- A short window (e.g. split screen) forces pagination even for a
    -- valid name within the engine's 64-byte limit.
    modify fun s => { s with io := { s.io with screen := pure #[540, 900, 128, 63, 420] }, W := 540, bgRow := Paint.solid Row.bg 540 }
    steps 1
    let s ← get
    let all := Label.lines s.font s.dim s.W longName
    let cap := Label.capacity s.dim (viewH s)
    check "label fixture spans multiple pages" (all.size > cap)
    let mut seen : Array Text.Line := #[]
    for p in [0:(all.size + cap - 1) / cap] do
      let s ← get
      check s!"full label page {p} is reached through Next" (s.labelPage == p && s.page == .label)
      seen := seen ++ Label.window all cap s.labelPage
      if p == 0 || (p + 1) * cap ≥ all.size then
        writePpm (dir ++ s!"/label-{p}.ppm") s.W (← screenOf sm s.W s.Hs s.insetBot)
      let _ ← tap .labelNext
    check "reading every page reaches every laid-out glyph" ((seen.map fun l => l.map fun g => (g.c, g.x)) == (all.map fun l => l.map fun g => (g.c, g.x)))
    let copied ← tap .copyLabel
    check "Copy full text uses the exact source string" (copied && (← sm.replies.get).contains s!"copied {longName}")
    let last := (← get).labelPage
    let _ ← tap .labelPrev
    check "Previous returns to the preceding label page" ((← get).labelPage == last - 1)
    back
    modify fun s => { s with io := io, W := 1080, bgRow := Paint.solid Row.bg 1080 }
    steps 2
    -- Compact switcher entries also disclose the original by long press.
    openPage .switcher; steps 2
    let idx := (← get).comms.findIdx? (·.acc == first) |>.getD 0
    let touched ← tap (.switchTo idx) true
    check "switcher long press discloses without switching" (touched && (← get).page == .label && (← get).cur == first && (← get).labelText == longName)
    back; back; steps 2
    let touched ← tap (.person 0) true
    check "people row long press discloses its full name" (touched && (← get).page == .label && (← get).labelText == "A very long member name that needs its full profile label")
    back; steps 2
    let s ← get
    let a := drawPage s.font s.bgRow none { pageIn s with online := #[false] }
    let b := drawPage s.font s.bgRow none { pageIn s with online := #[true] }
    check "stored sessions cannot paint presence on the home page" (a.1.bmp.rows == b.1.bmp.rows)
    let _ ← tap (.openChannel 0)
    sm.cmds.modify (·.push "chaos 80")
    steps 2; waitIdle sm; steps 15
    check "conversation has 80 real messages" ((← get).total == 80)
    -- Late row measurements and an arrival while scrolled back.
    sm.b.set 4000; steps 12
    let old ← get
    let some (anchor, _) := rowAt old old.b | check "a visible scroll anchor exists" false; return
    let before := position old anchor
    check "reader is away from the bottom on a painted row" (old.b > 4 && before.isSome && (old.rows[anchor]?.bind (·.shown)).isSome)
    let text := "Arriving while reading older messages\nwith a second line\nand a third"
    let sent ← sendText text
    steps 1
    check "pending arrival keeps the visible row at the same pixel" (sent && position (← get) anchor == before)
    waitIdle sm
    check "filing that arrival still keeps the same pixel" (position (← get) anchor == before)
    -- An incoming notice, without the optimistic outbox path.
    let s ← get
    let (key, _) ← readView (Community.currentKey s.me.c) #[]
    let some key := key | check "community key is available" false; return
    let post := sealedPost s.me.c s.me.adm s.me.dev key (← Engine.Crypto.randomBytes 24)
      "Incoming through the writer notice".toUTF8 (newestTime s + 1)
    s.wr.submit ⟨[post], true⟩
    waitIdle sm
    check "incoming writer notice preserves the visible row" ((← get).total == 82 && position (← get) anchor == before)
    -- More arrivals than the old fetch limit must not evict the anchor.
    let s ← get
    let count := s.limit + 5
    let photoId := (s.rows.toList.find? fun (_, r) => !r.lay.pics.isEmpty).map (·.1)
    let posts ← (List.range count).mapM fun i => do
      let nonce ← Engine.Crypto.randomBytes 24
      pure (sealedPost s.me.c s.me.adm s.me.dev key nonce s!"Burst message {i}".toUTF8 (newestTime s + 1 + i))
    s.wr.submit ⟨posts, true⟩
    -- Let the whole batch commit before the next app frame.
    for _ in [0:10000] do
      if (← s.wr.busy.get) == 0 then break
      IO.sleep 1
    steps 3; waitIdle sm
    check "a burst larger than the fetch window retains the visible message"
      ((← get).total == 82 + count && position (← get) anchor == before)
    sm.b.set 0; steps 3
    let _ ← sendText "Pinned arrival"
    steps 3; waitIdle sm
    check "arrival at the bottom stays pinned" ((← get).b == 0 && (← get).total == 83 + count)
    -- Copy the actual row via its long press and the sheet's copy button.
    let s ← get
    let m := s.ids[0]!.2
    let y := bottomPad + heightOf s m / 2
    let _ ← step [.long .list 300 y.toUInt32]
    check "message long press selects one row and opens one sheet" ((← get).selected == some m && (← get).sheet.isSome)
    let q := Sheet.quick (← get).dim (← get).W
    let _ ← step [.tap .composer 300 (q.copyY + q.copyH / 2).toUInt32]
    check "message Copy reaches the clipboard and closes the sheet" ((← sm.replies.get).contains "copied Pinned arrival" && (← get).sheet.isNone)
    -- Locate a photo, then long press inside its actual laid-out box.
    let s ← get
    if let some m := photoId then
      if let some i := s.ids.findIdx? (·.2 == m) then sm.b.set (bottoms s).1[i]!.toFloat
    steps 12
    let s ← get
    let photo := s.rows.toList.find? fun (m, _) => some m == photoId
    if let some (m, row) := photo then
      let bx := row.lay.pics[0]!
      let i := s.ids.findIdx? (·.2 == m) |>.getD 0
      let (bs, _) := bottoms s
      let y := bs[i]! + row.lay.h - 1 - (bx.y + bx.h / 2)
      sm.b.set (y - viewH s / 2).toFloat
      steps 3
      let s ← get
      check "photo press is inside the visible viewport" (s.b ≤ y && y < s.b + viewH s)
      let _ ← step [.long .list (bx.x + bx.w / 2).toUInt32 y.toUInt32]
      check "long press inside a photo opens that message's reactions" ((← get).selected == some m && (← get).sheet.isSome)
      let q := Sheet.quick (← get).dim (← get).W
      let _ ← step [.tap .composer (q.keys.x0 + q.keys.key / 2).toUInt32 (q.keys.y0 + q.keys.key / 2).toUInt32]
      waitIdle sm
      check "the photo reaction is written and the sheet closes" ((← get).sheet.isNone && ((← get).rows[m]?.map (·.data.tallies.any (fun t => t.mine && t.emoji == "👍"))).getD false)
    else check "photo fixture is mounted" false
    -- Existing navigation invariant: switching by acceptance clears the
    -- sheet and its back stack; Back cannot revive the old community.
    sm.b.set 0; steps 3
    let _ ← step [.long .list 300 (bottomPad + 30).toUInt32]
    check "switch fixture has an open sheet" ((← get).sheet.isSome)
    sm.cmds.modify (·.push "found second|Other")
    steps 3; waitIdle sm
    let second := (← get).me.acc
    switchToAcc first; steps 3
    check "switch by acceptance closes transient message UI" ((← get).cur == first && (← get).sheet.isNone && (← get).selected.isNone && (← get).backStack.isEmpty)
    back; steps 2
    check "Back after a switch stays in the chosen community" ((← get).cur == first && first != second)
    pure ()).run s
  IO.println s!"UX: {← checks.get} checks, {← fails.get} failures"
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
