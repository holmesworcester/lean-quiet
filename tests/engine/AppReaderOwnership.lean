/- Actual threaded Reader pass survives a later App frame rollback. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open App Engine Data Tests
namespace AppReaderOwnership

/-- Test-only observation of the original native task and cancellation cap. -/
unsafe def sameWorker (a b : Reader.Worker) : Bool := ptrEq a.done b.done && ptrEq a.stopped b.stopped

unsafe def run (dir : String) (checks : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/app.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let armed ← IO.mkRef false
  let reapFault ← IO.mkRef false
  let entered ← IO.mkRef false
  let enabled ← IO.mkRef (pure false : IO Bool)
  let released ← IO.mkRef false
  let release ← IO.Promise.new
  let captured ← IO.mkRef (none : Option Reader.Worker)
  let replacement ← IO.mkRef (none : Option Reader.Worker)
  let io := { sm.io with
    screen := do
      if ← reapFault.modifyGet fun x => (x, false) then
        throw (IO.userError "expected Reader ownership screen failure")
      sm.io.screen
    scroll := fun h v => do
    if ← armed.modifyGet fun x => (x, false) then
      unless ← PublicationFixture.waitFor 2000 entered.get do
        throw (IO.userError "fixture did not observe the actual Reader pass")
      throw (IO.userError "expected Reader ownership frame failure")
    sm.io.scroll h v }
  let initial ← App.start io (← sm.viewport.get) path
  let initial := (← (App.step []).run initial).2
  let initial := (← (App.step []).run initial).2
  let original := { initial with threaded := true }
  checks.ok "fixture uses the already-current mounted page before starting its Reader"
    (original.mountedPage == some (original.page, original.cur))
  let op := PublicationFixture.root "actual Reader rollback ownership"
  original.sh.act op.id do
    discard <| Reader.read (Q.op op.id)
    let can := (← get).enabled
    enabled.modify (fun _ => can)
    entered.modify (fun _ => true)
    discard <| IO.wait release.result!
    released.modify (fun _ => true)
    return ⟨[op]⟩
  armed.modify (fun _ => true)
  try
    -- Observe the capability returned by the actual mount/resume stage.
    -- Then a later real frame callback fails in the same outer StateT.
    let action : App.M Unit := do
      App.mountPage
      let worker := (← get).reader
      captured.modify (fun _ => worker)
      discard <| App.step []
    let result ← (action.run original).toBaseIO
    checks.ok "actual later App frame callback throws after the Reader entered its SQLite pass"
      (match result with | .error e => e.toString.endsWith "expected Reader ownership frame failure" | _ => false)
    let observed ← captured.get
    checks.ok "actual mount/resume returned the original Worker capability" observed.isSome
    let some worker := observed | return
    checks.ok "discarded StateT result leaves the original borrowed Reader fields empty"
      (original.reader.isNone && original.rst.isSome)
    checks.ok "the original threaded Reader is actually blocked inside its admitted intent"
      ((← entered.get) && !(← released.get) && (← (← enabled.get)))
    let stopped := (← (App.suspend 100).run original).2
    checks.ok "suspend revokes the original in-flight Reader despite frame rollback"
      (!(← (← enabled.get)))
    checks.ok "suspend retains the original unfinished Reader task for later reap"
      stopped.readerStop.isSome
    let originalCap := stopped.readerStop.any fun retained => sameWorker retained worker
    checks.ok "the retained task is exactly the original Worker and its stop flag" originalCap
    unless originalCap do return
    let beforeRepeat ← stopped.readerOwner.snapshot
    let repeated := (← (App.suspend 20).run stopped).2
    let afterRepeat ← repeated.readerOwner.snapshot
    let same := repeated.readerStop.any fun retained => sameWorker retained worker
    checks.ok "another suspend keeps exactly the original retiring Worker" same
    checks.ok "another suspend keeps the replacement board and owner generation"
      (ptrEq stopped.sh repeated.sh && beforeRepeat.generation == afterRepeat.generation)
    checks.ok "no replacement Worker starts while the original pass is still held"
      (afterRepeat.active.isNone && !(← IO.hasFinished worker.done))
    unless same do return
    release.resolve ()
    checks.ok "the actual original Reader intent returns after its finite barrier releases"
      (← PublicationFixture.waitFor 2000 released.get)
    let finished ← PublicationFixture.waitFor 2000 (IO.hasFinished worker.done)
    checks.ok "the original Reader worker finishes after App revocation" finished
    checks.ok "revoked in-flight work does not publish its signed write after suspend"
      (!((← original.sh.done.get).any fun (_, w) => w.any fun w => w.ops.any (·.id == op.id)))
    unless finished do return
    let .ok reader := worker.done.get | throw (IO.userError "original Reader failed instead of returning its state")
    reapFault.modify (fun _ => true)
    -- stepCore really reaps before asking its screen callback and mounting.
    let reaped ← ((App.step []).run repeated).toBaseIO
    checks.ok "actual screen callback fails after reaping and before a replacement mount"
      (match reaped with | .error e => e.toString.endsWith "expected Reader ownership screen failure" | _ => false)
    let ready ← repeated.readerOwner.snapshot
    let retained := ready.ready.any fun r => ptrEq r.rd reader.rd
    checks.ok "shared ownership retains the original Reader connection after reap rollback" retained
    checks.ok "the completed original Worker is reaped exactly once"
      (ready.active.isNone && ready.retiring.isNone && ready.generation == afterRepeat.generation + 1)
    unless retained do return
    let reentered := (← App.reap.run repeated).2
    checks.ok "stale frame fields recover the same completed Reader connection"
      (reentered.readerStop.isNone && reentered.rst.any fun r => ptrEq r.rd reader.rd)
    reentered.wr.submit ⟨[op], true⟩
    checks.ok "the fixture commits its real signed operation through the actual Writer"
      (← PublicationFixture.waitFor 2000 (PublicationFixture.valid reentered.rd op))
    let some idle := reentered.rst | throw (IO.userError "missing recovered Reader state")
    let (answer, cached) ← (Reader.read (Q.op op.id)).run idle
    checks.ok "the recovered connection performs an actual nonempty signed-byte read"
      (answer == .bytes (some op.bytes) && cached.live.entries.contains (Q.op op.id))
    let cachedApp := { reentered with rst := some cached }
    let cacheKept := (← App.reap.run cachedApp).2
    checks.ok "same-generation polling retains synchronous Reader cache progress"
      (cacheKept.rst.any fun r => r.live.entries.contains (Q.op op.id) && r.live.reads == cached.live.reads)
    let restarted := (← App.mountPage.run cacheKept).2
    replacement.modify (fun _ => restarted.reader)
    checks.ok "a real replacement Worker starts after the original is reaped" restarted.reader.isSome
    let some next := restarted.reader | return
    checks.ok "the new lifetime has a distinct Worker and cancellation flag" (!sameWorker worker next)
    let want := Reader.Want.slices [op.id]
    restarted.sh.setWants #[want]
    checks.ok "the replacement Worker publishes exact committed bytes through its actual board"
      (← PublicationFixture.waitFor 2000 do
        return ((← restarted.sh.board.get).get? want).any fun (value, _) => value == .slices (some [op.bytes]))
    let closed := (← (App.suspend 100).run restarted).2
    checks.ok "actual App shutdown revokes and finishes the replacement Worker"
      ((← next.stopped.get) && (← PublicationFixture.waitFor 2000 (IO.hasFinished next.done)))
    discard <| App.reap.run closed
    let final ← closed.readerOwner.snapshot
    checks.ok "final reap leaves no active or retiring Worker cap"
      (final.active.isNone && final.retiring.isNone && final.ready.isSome)
  finally
    release.resolve ()
    if let some worker ← captured.get then
      worker.requestStop
      unless ← PublicationFixture.waitFor 2000 (IO.hasFinished worker.done) do
        throw (IO.userError "fixture could not reap its original Reader after explicit cleanup")
      discard <| IO.wait worker.done
    if let some worker ← replacement.get then
      worker.requestStop
      unless ← PublicationFixture.waitFor 2000 (IO.hasFinished worker.done) do
        throw (IO.userError "fixture could not reap its replacement Reader after explicit cleanup")
      discard <| IO.wait worker.done

end AppReaderOwnership

unsafe def main (args : List String) : IO UInt32 := do
  let checks ← Checks.new
  try
    AppReaderOwnership.run (args.headD "out/app-reader-ownership/probe") checks
    let code ← checks.finish "app-reader-ownership"
    (← IO.getStdout).flush
    IO.Process.exit code.toUInt8
  catch e =>
    IO.eprintln s!"unexpected Reader ownership fixture error: {e}"
    (← IO.getStderr).flush
    IO.Process.exit 2
