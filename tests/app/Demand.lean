/- Real worker/reader races with barriers, not timing-dependent sleeps.
The pool executes the same queue, ticket and publication code as App. -/
import app.community.channel.message.attachment.Screen
import app.Screen
import platforms.headless.Sim
import tests.app.Presentation
import tests.engine.Checks

open Engine Community Data Tests

namespace DemandTest

def await (what : String) (condition : IO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then throw (IO.userError s!"timeout: {what}")
    IO.sleep 1

def need (key : Nat) (owner : String := "message") (visible := true) : Demand.Need Nat :=
  ⟨[owner.toUTF8], key, visible⟩

def result (h : Work.Handle Nat Nat) : IO (Option Nat) := do
  await "worker completion" (IO.hasFinished h.result)
  return h.result.get

def queue (ck : Checks) : IO Unit := do
  let pool ← Work.Pool.new (K := Nat) (V := Nat)
  pool.pause true
  let calls ← IO.mkRef (#[] : Array Nat)
  let mut old := #[]
  for i in [0:40] do
    old := old.push (← pool.request (need i) fun _ => do calls.modify (·.push i); return some i)
  let latest ← pool.request (need 100) fun _ => do calls.modify (·.push 100); return some 100
  -- A background barrier sits behind any accidentally retained obsolete
  -- jobs. Waiting only for the visible result would race with those jobs:
  -- priority correctly runs the visible result first even in that mutant.
  let drained ← pool.request (need 101 "drain" false) fun _ => do calls.modify (·.push 101); return some 101
  pool.reconcile [need 100, need 101 "drain" false]
  pool.pause false
  let newest ← result latest
  discard <| result drained
  ck.ok "fast viewport changes discard every obsolete queued action" (newest == some 100 && (← calls.get) == #[100, 101])
  let mut retired := true
  for h in old do retired := retired && (← result h).isNone
  ck.ok "retired queued handles finish without waiting for abandoned work" retired
  let stats ← pool.stats
  ck.ok "only the final viewport and drain barrier spend work steps" (stats.steps == 2 && stats.cancelled == 40)

  pool.pause true
  let shared ← pool.request (need 200 "author-a") fun _ => return some 200
  let other ← pool.request (need 200 "author-b") fun _ => return some 999
  pool.reconcile [need 200 "author-b"]
  pool.pause false
  ck.ok "two components share one job and one ticket" (shared.ticket == other.ticket && (← result other) == some 200)
  ck.ok "removing one owner preserves the other owner's result" ((← result shared) == some 200)

  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let steps ← IO.mkRef 0
  let stale ← pool.request (need 300) fun _ => do
    steps.modify (· + 1)
    entered.set true
    await "release old step" release.get
    return none
  await "old work started" entered.get
  pool.reconcile []
  let remount ← pool.request (need 300) fun _ => return some 301
  release.set true
  ck.ok "remount uses a fresh ticket even for the same query key" (remount.ticket != stale.ticket)
  ck.ok "in-flight obsolete continuation runs no second step" ((← result stale).isNone && (← steps.get) == 1)
  ck.ok "remounted component receives its own result" ((← result remount) == some 301)

  pool.pause true
  calls.set #[]
  let slow ← pool.request (need 400 "prefetch" false) fun _ => do calls.modify (·.push 400); return some 400
  let fast ← pool.request (need 401 "picture" true) fun _ => do calls.modify (·.push 401); return some 401
  pool.reconcile [need 400 "prefetch" false, need 401 "picture" true]
  pool.pause false
  discard <| result slow
  discard <| result fast
  ck.ok "visible work runs before earlier prefetch" ((← calls.get) == #[401, 400])

  pool.pause true
  calls.set #[]
  let mut hs := #[]
  for i in [500:503] do
    let count ← IO.mkRef 0
    hs := hs.push (← pool.request (need i) fun _ => do
      calls.modify (·.push i)
      count.modify (· + 1)
      return if (← count.get) == 3 then some i else none)
  -- Repeated reconciliations in a different order cannot reset progress
  -- or move established requests behind newer work.
  for _ in [0:20] do pool.reconcile [need 502, need 500, need 501]
  pool.pause false
  for h in hs do discard <| result h
  ck.ok "continuations retain progress and rotate fairly within a class"
    ((← calls.get) == #[500, 501, 502, 500, 501, 502, 500, 501, 502])

def pixels (ck : Checks) : IO Unit := do
  let src : Image.Src := ⟨7, 11, (List.range 77).toArray.map fun i =>
    ((i * 73271).toUInt32 <<< (8 : UInt32)) ||| (80 + i % 176).toUInt32⟩
  for (w, h) in [(1, 1), (3, 5), (19, 27), (31, 4), (4, 31)] do
    for preview in [false, true] do
      let action ← Raster.image (fun _ => some src) w h .light preview
      let mut value := none
      for _ in [0:h + 2] do
        value ← action ()
        if value.isSome then break
      let reference := Image.scaled src w h (Palette.color .light .bg)
      let reference := if preview then Arrival.soften (Palette.color .light .bg) reference else reference
      ck.ok s!"cooperative image equals production scaling {w}x{h} preview={preview}"
        (value.map (·.rows) == some reference.rows)

def reader (ck : Checks) : IO Unit := do
  let db ← openDb ":memory:"
  db.filings
  let c := "reader-cancellation".toUTF8
  for i in [0:40] do
    let f : SF := .inl (.inl (.admission c s!"user-{i}".toUTF8 s!"device-{i}".toUTF8 s!"node-{i}".toUTF8))
    (show SqlM SF Unit from do
      Store.setStatus s!"admission-{i}".toUTF8 (.valid f)
      for k in fam.keys f do Store.index k s!"admission-{i}".toUTF8).run db
  let sh ← Reader.Shared.new (← IO.mkRef 1)
  let old := Reader.Want.members c c
  let newest := Reader.Want.people c
  sh.setWants #[old]
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let queries ← IO.mkRef 0
  let initial : Reader.St := { rd := db, afterQuery := fun _ => do
    queries.modify (· + 1)
    if (← queries.get) == 1 then
      entered.set true
      await "reader first query release" release.get }
  let pending ← IO.asTask (prio := .dedicated) ((Reader.pass sh).run initial)
  await "actual first SQLite query" entered.get
  sh.setWants #[newest]
  release.set true
  let (_, state) ← match ← IO.wait pending with
    | .ok s => pure s
    | .error e => throw e
  ck.ok "superseded reader stops at the next query boundary" ((← queries.get) == 1)
  ck.ok "superseded reader cannot publish a partial or obsolete answer" (((← sh.board.get).get? old).isNone)
  let (_, state) ← (Reader.pass sh).run { state with afterQuery := fun _ => pure () }
  ck.ok "latest viewport receives actual SQLite content on the next pass"
    (((← sh.board.get).get? newest).map (·.1) == some (.people 40 true))
  let some ticket := (← sh.plan.get).ticket newest | throw (IO.userError "no current ticket")
  sh.setWants #[]
  sh.setWants #[newest]
  sh.publish ticket (.people 999 false)
  ck.ok "reader publication rejects completion across unmount and remount"
    (((← sh.board.get).get? newest).isNone)
  discard <| (Reader.pass sh).run state
  ck.ok "unmount and remount between passes refills the revoked board answer"
    (((← sh.board.get).get? newest).map (·.1) == some (.people 40 true))

  -- A repeated read failure must not restore an earlier scheduling position
  -- on every worker pass. Inject after a real query; the transaction still
  -- takes the production rollback/retry path, with no sleeps deciding order.
  let bad := Reader.Want.people "failing-query".toUTF8
  let (_, probe) ← (Reader.evalLogged bad).run { rd := db }
  let some badQuery := probe.log[0]? | throw (IO.userError "failure probe made no query")
  let retry ← Reader.Shared.new (← IO.mkRef 1)
  retry.setWants #[bad, newest]
  let failures ← IO.mkRef 0
  let stopped ← IO.mkRef false
  let enabled : IO Bool := do return !(← stopped.get)
  let initial : Reader.St := {
    rd := db
    enabled
    afterQuery := fun q => do
      if q == badQuery then
        failures.modify (· + 1)
        if (← failures.get) == 3 then stopped.modify (fun _ => true)
        throw (IO.userError "injected repeatable failure after real SQLite read") }
  let worker ← IO.asTask (prio := .dedicated) (Reader.work retry stopped initial)
  await "three failed reader attempts" (IO.hasFinished worker)
  match ← IO.wait worker with
  | .error e => throw e
  | .ok _ => pure ()
  ck.ok "repeatable read failure cannot starve a retained later query across transaction rollback"
    (((← retry.board.get).get? newest).map (·.1) == some (.people 40 true))
  ck.ok "failed query publishes no invented answer and retries after yielding its position"
    ((← failures.get) == 3 && ((← retry.board.get).get? bad).isNone)

/-- Diagnostic counterexample, not a fix: actual worker completes every
paint, yet presentation's version reconciliation rejects each older result.
Only reaction tallies change; the committed message text stays unchanged. -/
def paintChurn (ck : Checks) : IO Unit := do
  let font ← Font.load (density := 160)
  let dm : Row.Dim := ⟨160, font.cell, .dark, none⟩
  let width := 420
  let background := Paint.solid (Palette.color .dark .bg) width
  let pool ← Work.Pool.new (K := Raster.Key) (V := Paint.Bitmap)
  let owner := Raster.messageOwner "community".toUTF8 "own-post".toUTF8
  let entered ← IO.mkRef (0 : Nat)
  let releases ← IO.mkRef (0 : Nat)
  let painted ← IO.mkRef (0 : Nat)
  let data (version : Nat) : Row.RowData :=
    { name := "Alice", avatar := none, text := "My committed message", time := 1,
      pics := [], tallies := [⟨"+1", version, false⟩], pending := false,
      selected := false, own := true }
  let request (version : Nat) := do
    let key := Raster.Key.row 1 "own-post".toUTF8 version [false] .dark
    let need : Demand.Need Raster.Key := ⟨owner, key, true⟩
    let d := data version
    let lay := Row.layout font dm width d
    let handle ← pool.request need fun _ => do
      let bitmap := Row.paint font dm width background d lay none #[]
      -- Force the actual paint before the barrier; publication stays in
      -- Work.run, with its real current-ticket check after action return.
      unless bitmap.rows.size > 0 do throw (IO.userError "empty row paint")
      painted.modify (· + 1)
      entered.set version
      await "release completed row paint" do return (← releases.get) ≥ version
      return some bitmap
    return (need, handle)
  let (firstNeed, first) ← request 1
  pool.reconcile [firstNeed]
  let mut current := first
  let mut cancelled := 0
  let mut shown : Option Paint.Bitmap := none
  for version in [1:9] do
    await "row paint reached publication barrier" do return (← entered.get) == version
    let (nextNeed, next) ← request (version + 1)
    -- The exact API App.present calls with this frame's declared key.
    pool.reconcile [nextNeed]
    releases.set version
    await "obsolete paint resolved" (IO.hasFinished current.result)
    let value ← current.value
    if value.isNone then cancelled := cancelled + 1
    shown := value.orElse fun _ => shown
    current := next
  ck.ok "eight completed actual paints produce no first shown bitmap under version churn"
    (cancelled == 8 && shown.isNone && (← painted.get) ≥ 8)
  ck.ok "only reaction tally changed; own body remains committed and identical"
    ((List.range 9).all fun v => (data (v+1)).text == (data 1).text && !(data (v+1)).pending)
  await "final stable paint started" do return (← entered.get) == 9
  releases.set 9
  await "stable paint publishes" (IO.hasFinished current.result)
  let final ← current.value
  ck.ok "stopping invalidation permits the exact current row bitmap"
    (final.any fun bitmap => bitmap.rows == (Row.paint font dm width background
      (data 9) (Row.layout font dm width (data 9)) none #[]).rows)
  let stats ← pool.stats
  ck.ok "worker made progress throughout: eight cancellations then one publication"
    (stats.steps == 9 && stats.cancelled == 8 && stats.completed == 1)


/-- The exact request selector called by App.paintRow retains the first
committed snapshot while newer reaction counts keep arriving. This uses
actual raster actions and end-frame reconciliation, with barriers rather
than worker timing. -/
def paintCoalescing (ck : Checks) : IO Unit := do
  let font ← Font.load (density := 160)
  let dm : Row.Dim := ⟨160, font.cell, .dark, none⟩
  let width := 420
  let background := Paint.solid (Palette.color .dark .bg) width
  let pool ← Work.Pool.new (K := Raster.Key) (V := Paint.Bitmap)
  let owner := Raster.messageOwner "community".toUTF8 "own-post".toUTF8
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let calls ← IO.mkRef (0 : Nat)
  let data (version : Nat) : Row.RowData :=
    { name := "Alice", avatar := none, text := "My committed message", time := 1,
      pics := [], tallies := [⟨"+1", version, false⟩], pending := false,
      selected := false, own := true }
  let request (first : Bool) (old : Option Raster.RowPaint.Flight) (version : Nat) := do
    let d := data version
    let lay := Row.layout font dm width d
    let stamp := Raster.RowPaint.stamp 1 "own-post".toUTF8 width dm background d [false]
    let answer ← Raster.RowPaint.request pool owner true first old stamp version d lay #[] fun _ => do
      let bitmap := Row.paint font dm width background d lay none #[]
      unless bitmap.rows.size > 0 do throw (IO.userError "empty coalesced row paint")
      calls.modify (· + 1)
      if version == 1 then
        entered.set true
        await "first committed paint release" release.get
      return some bitmap
    pool.reconcile [⟨owner, answer.1.handle.ticket.key, true⟩]
    return answer
  let (first, _) ← request true none 1
  await "first committed paint computed" entered.get
  let mut flight := first
  let mut kept := true
  for version in [2:9] do
    let (next, value) ← request true (some flight) version
    kept := kept && next.handle.ticket == first.handle.ticket && value.isNone
    flight := next
  ck.ok "reaction churn preserves the original admitted ticket and queue position"
    (kept && (← calls.get) == 1 && (← pool.stats).started == 1)
  -- Updates continue across release and collection: no stable-version
  -- interval is needed for the first committed body's publication.
  release.set true
  await "retained committed paint publishes" (IO.hasFinished first.handle.result)
  let (collected, value) ← request true (some flight) 9
  let exactFirst := Row.paint font dm width background (data 1)
    (Row.layout font dm width (data 1)) none #[]
  ck.ok "first committed body appears during a newer cosmetic version"
    (collected.version == 1 && value.any (·.rows == exactFirst.rows) && data 9 != data 1)
  let (latest, _) ← request false (some collected) 10
  await "latest repaint completes" (IO.hasFinished latest.handle.result)
  let (latestAgain, latestValue) ← request false (some latest) 10
  let exactLatest := Row.paint font dm width background (data 10)
    (Row.layout font dm width (data 10)) none #[]
  ck.ok "subsequent repaint preserves the exact latest bitmap oracle"
    (latestAgain.version == 10 && latestAgain.handle.ticket == latest.handle.ticket &&
      latestValue.any (·.rows == exactLatest.rows))
  let stats ← pool.stats
  ck.ok "coalescing computes one initial and one latest paint without cancellation"
    (stats.started == 2 && stats.steps == 2 && stats.completed == 2 && stats.cancelled == 0)

/-- Each incompatible input revokes a real blocked paint before it can
publish. Deliberately reuse the version to ensure replacement identity is
not accidentally inherited from the old bitmap's key. -/
def paintInvalidation (ck : Checks) : IO Unit := do
  let font ← Font.load (density := 160)
  let dm : Row.Dim := ⟨160, font.cell, .dark, none⟩
  let width := 420
  let background := Paint.solid (Palette.color .dark .bg) width
  let d : Row.RowData :=
    { name := "Alice", avatar := none, text := "A committed message", time := 1,
      pics := [], tallies := [], pending := false, selected := false, own := true }
  let lay := Row.layout font dm width d
  let base := Raster.RowPaint.stamp 1 "own-post".toUTF8 width dm background d [false]
  let changes : List (String × Raster.RowPaint.Stamp) := [
    ("generation", { base with generation := 2 }),
    ("message identity", { base with message := "another-post".toUTF8 }),
    ("message body", { base with body := { base.body with text := "replacement" } }),
    ("pending state", { base with body := { base.body with pending := true } }),
    ("selection", { base with body := { base.body with selected := true } }),
    ("width", { base with width := width + 1 }),
    ("density", { base with dim := { dm with dpi := 200 } }),
    ("theme", { base with dim := { dm with theme := .light } }),
    ("background", { base with background := "other background".toUTF8 }),
    ("attachment readiness", { base with ready := [false, true] })]
  for (name, changed) in changes do
    let pool ← Work.Pool.new (K := Raster.Key) (V := Paint.Bitmap)
    let owner := Raster.messageOwner "community".toUTF8 "own-post".toUTF8
    let entered ← IO.mkRef false
    let release ← IO.mkRef false
    let (old, _) ← Raster.RowPaint.request pool owner true true none base 1 d lay #[] fun _ => do
      let bitmap := Row.paint font dm width background d lay none #[]
      unless bitmap.rows.size > 0 do throw (IO.userError "empty invalidation paint")
      entered.set true
      await "incompatible paint release" release.get
      return some bitmap
    await "incompatible paint started" entered.get
    let (fresh, _) ← Raster.RowPaint.request pool owner true true (some old) changed 1 d lay #[]
      fun _ => pure (some (Row.paint font dm width background d lay none #[]))
    pool.reconcile [⟨owner, fresh.handle.ticket.key, true⟩]
    release.set true
    await "revoked paint finishes" (IO.hasFinished old.handle.result)
    await "replacement paint finishes" (IO.hasFinished fresh.handle.result)
    ck.ok s!"{name} revokes the old in-flight publication"
      (old.handle.ticket != fresh.handle.ticket && (← old.handle.value).isNone &&
        (← fresh.handle.value).isSome)
  -- An unmount revokes even an otherwise compatible first-body snapshot.
  let pool ← Work.Pool.new (K := Raster.Key) (V := Paint.Bitmap)
  pool.pause true
  let owner := Raster.messageOwner "community".toUTF8 "own-post".toUTF8
  let action : Work.Action Paint.Bitmap := fun _ =>
    pure (some (Row.paint font dm width background d lay none #[]))
  let (old, _) ← Raster.RowPaint.request pool owner true true none base 1 d lay #[] action
  pool.reconcile []
  let (fresh, _) ← Raster.RowPaint.request pool owner true true (some old) base 1 d lay #[] action
  pool.pause false
  await "remounted paint finishes" (IO.hasFinished fresh.handle.result)
  ck.ok "unmount prevents reusing an otherwise compatible ticket"
    (old.handle.ticket != fresh.handle.ticket && (← old.handle.value).isNone &&
      (← fresh.handle.value).isSome)


/-- Real App send/SQLite commit/pending presentation, followed by controlled
child-board refills through actual mountChildren, paintRow and present. The
refills isolate ancillary churn deterministically; this is a native app-stage
regression, not a theorem about all TCP/reader scheduling. -/
def appPaintChurn (ck : Checks) : IO Unit := do
  let dir := s!"out/component-demand/paint-{← IO.Process.getPID}"
  IO.FS.createDirAll dir
  let sm ← Sim.new
  sm.viewport.set #[420, 900, 20, 20, 160]
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let (_, final) ← (show App.M Unit from do
    App.found "Paint progress" "Alice"
    App.openPage .chat
    waitIdle sm
    let writer := (← get).wr
    writer.setPaused true
    discard <| App.sendText "My committed body survives reaction churn"
    let mut optimistic : Option (Id × App.RowSt) := none
    for _ in [0:400] do
      steps 1
      let s ← get
      if let some p := s.rows.toList.find? (fun (_, r) => r.data.own && r.data.pending && r.shown.isSome) then
        optimistic := some p
        break
      IO.sleep 2
    let some (msg, pending) := optimistic | throw (IO.userError "optimistic bitmap missing")
    ck.ok "real paused writer produces an already shown optimistic bitmap"
      (pending.data.pending && pending.shown.isSome && !pending.shownCommitted)
    let entered ← IO.mkRef false
    let release ← IO.mkRef false
    let pool := (← get).raster
    let blockerNeed : Demand.Need Raster.Key :=
      ⟨["finite-worker-barrier".toUTF8], .row 0 "barrier".toUTF8 0 [] .dark, true⟩
    let blocker ← pool.request blockerNeed fun _ => do
      entered.set true
      await "finite app paint barrier" release.get
      return pending.shown
    await "app paint barrier entered" entered.get
    writer.setPaused false
    let mut committedFound : Option App.RowSt := none
    for _ in [0:400] do
      steps 1
      if let some row := (← get).rows[msg]? then
        if !row.data.pending && row.task.isSome then committedFound := some row; break
      IO.sleep 2
    let some committed := committedFound | throw (IO.userError "committed raster request missing")
    let some flight := committed.paintFlight | throw (IO.userError "committed flight missing")
    let s ← get
    let stored ← (Store.getOp msg : SqlM SF _).run s.rd
    ck.ok "actual commit replaces pending data while protecting the first committed paint"
      (stored.isSome && !committed.data.pending && !committed.shownCommitted &&
       committed.shown.isSome && !flight.data.pending && !(← IO.hasFinished flight.handle.result))
    let desired (version : Nat) : List Row.Tally :=
      if version % 2 == 0 then [] else
        (List.range 12).map fun i => ⟨s!"reaction-{i}", version + i, false⟩
    let getRow : App.M App.RowSt := do
      let some row := (← get).rows[msg]? | throw (IO.userError "mounted row missing")
      return row
    let childFrame (version : Nat) : App.M Unit := do
      let s ← get
      let tallies := desired version
      let mut board := (← s.sh.board.get)
        |>.put (.emojis s.me.c msg) (.emojis (tallies.map (·.emoji)))
        |>.put (.author s.me.c s.me.user) (.author s!"Alice {version}" false)
      for tally in tallies do
        board := board.put (.reaction s.me.c msg s.me.user tally.emoji) (.reaction tally)
      s.sh.board.set board
      modify fun s => { s with rasterNeeds := #[], queryNeeds := #[], querySeen := {} }
      App.mountChildren msg App.bottomPad 0 (App.viewH s)
      App.paintRow msg App.bottomPad 0 (App.viewH s)
      let s ← get
      discard <| App.present (App.listFrame s 0 (App.bottoms s).1) 0 false
    let mut retained := true
    let mut changesHeight := false
    for version in [1:9] do
      let desiredRow := { committed.data with tallies := desired version }
      changesHeight := changesHeight || (Row.layout s.font s.dim s.W desiredRow).h != committed.lay.h
      childFrame version
      let row ← getRow
      retained := retained && row.paintFlight.any (·.handle.ticket == flight.handle.ticket) &&
        row.lay.h == committed.lay.h && row.data == committed.data && !row.shownCommitted
    ck.ok "alternating reaction-row geometry cannot replace the committed snapshot"
      (changesHeight && retained && !(← IO.hasFinished flight.handle.result))
    release.set true
    await "finite app barrier resolved" (IO.hasFinished blocker.result)
    await "actual App committed paint completes" (IO.hasFinished flight.handle.result)
    let framesBefore ← sm.frames.get
    childFrame 9
    let first ← getRow
    let firstBmp := Row.paint s.font s.dim s.W s.bgRow flight.data flight.lay none flight.images
    ck.ok "committed body first publishes during continuing height-changing reaction churn"
      (first.shownCommitted && first.task.isNone && first.painted.1 == flight.version &&
        first.shown.any (·.rows == firstBmp.rows) && !first.data.pending &&
        (← sm.frames.get) > framesBefore)
    childFrame 11
    let adopted ← getRow
    let some latest := adopted.paintFlight | throw (IO.userError "latest app paint missing")
    ck.ok "after first publication the newest child data and geometry are adopted"
      (adopted.data.tallies != committed.data.tallies && adopted.lay.h != committed.lay.h &&
        latest.version == adopted.ver && latest.handle.ticket != flight.handle.ticket)
    await "latest App repaint completes" (IO.hasFinished latest.handle.result)
    modify fun s => { s with rasterNeeds := #[] }
    App.paintRow msg App.bottomPad 0 (App.viewH (← get))
    let s ← get
    discard <| App.present (App.listFrame s 0 (App.bottoms s).1) 0 false
    let latestRow ← getRow
    ck.ok "App still publishes the exact latest data-version bitmap after catch-up"
      (latestRow.task.isNone && latestRow.painted.1 == latestRow.ver &&
        latestRow.shown.any (fun bitmap => bitmap.rows ==
          (Row.paint s.font s.dim s.W s.bgRow latestRow.data latestRow.lay none #[]).rows))
    -- A known inaccessible row must be removed before it can declare any
    -- retained raster demand or be composed into the next presentation.
    let board := (← s.sh.board.get).put (.row s.me.c s.me.adm msg) (.row none)
    App.mount board msg
    modify fun s => { s with rasterNeeds := #[] }
    App.paintRow msg
    let s ← get
    discard <| App.present (App.listFrame s 0 (App.bottoms s).1) 0 false
    ck.ok "an explicit unreadable-row answer removes the cached bitmap and its work"
      (!(← get).rows.contains msg && (← get).rasterNeeds.isEmpty &&
        !(← pool.state.atomically do return (← get).plan.current latest.handle.ticket))
    ).run initial
  final.raster.reconcile []


/-- Hold an actual App.step in frame assembly while a previously admitted
row paint is queued behind a finite worker action. Back-to-back frames must
not disable the worker's next selection. The barriers make the interleaving
deterministic; no relative timing of the UI and worker is assumed. -/
def appWorkerProgress (ck : Checks) : IO Unit := do
  let dir := s!"out/component-demand/worker-{← IO.Process.getPID}"
  IO.FS.createDirAll dir
  let sm ← Sim.new
  sm.viewport.set #[420, 900, 20, 20, 160]
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let entered ← IO.mkRef false
  let release ← IO.mkRef false
  let frameEntered ← IO.mkRef false
  let frameRelease ← IO.mkRef false
  let pool := initial.raster
  let blocker ← pool.request ⟨["worker-barrier".toUTF8], .row 0 "barrier".toUTF8 0 [] .dark, true⟩ fun _ => do
    entered.set true
    await "worker-selection barrier release" release.get
    return some default
  await "worker-selection barrier entered" entered.get
  let msg := "queued-own-row".toUTF8
  let d : Row.RowData :=
    { name := "Alice", avatar := none, text := "A retained body needs worker service", time := 1,
      pics := [], tallies := [], pending := false, selected := false, own := true }
  let lay := Row.layout initial.font initial.dim initial.W d
  let row : App.RowSt := { data := d, lay, painted := (0, []), task := none, shown := none, ver := 1 }
  let (_, queued) ← (App.paintRow msg).run { initial with page := .chat, rows := ({} : Std.HashMap Id App.RowSt).insert msg row }
  let some flight := (queued.rows[msg]?).bind (·.paintFlight) | throw (IO.userError "queued App paint missing")
  let frameIO := { queued.io with nowUs := do
    if !(← frameEntered.get) then
      frameEntered.set true
      await "frame assembly release" frameRelease.get
    return (← IO.monoNanosNow).toUInt64 / 1000 }
  let frame ← IO.asTask (prio := .dedicated) ((App.step []).run { queued with io := frameIO })
  await "actual frame assembly entered" frameEntered.get
  let enabled ← pool.state.atomically do return !(← get).paused
  release.set true
  let mut completedInside := false
  if enabled then
    await "retained App row paints during frame assembly" (IO.hasFinished flight.handle.result)
    completedInside := (← flight.handle.value).isSome && !(← frameRelease.get)
  frameRelease.set true
  let (_, final) ← match ← IO.wait frame with
    | .ok state => pure state
    | .error e => throw e
  await "worker-selection barrier finishes" (IO.hasFinished blocker.result)
  ck.ok "actual App.step permits retained raster progress during frame assembly"
    (enabled && completedInside)
  final.raster.reconcile []


end DemandTest

def main : IO UInt32 := do
  let ck ← Checks.new
  let code ← try
    DemandTest.queue ck
    DemandTest.pixels ck
    DemandTest.reader ck
    DemandTest.paintChurn ck
    DemandTest.paintCoalescing ck
    DemandTest.paintInvalidation ck
    DemandTest.appPaintChurn ck
    DemandTest.appWorkerProgress ck
    PresentationTests.run ck
    ck.finish "component-demand"
  catch e => IO.eprintln s!"component-demand: {e}"; pure 1
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
