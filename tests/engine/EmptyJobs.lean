/- Actual empty maintenance writes must not occupy runtime queues. -/
import platforms.headless.Sim
import tests.engine.PublicationFixture
import tests.engine.Checks

open Engine Data App Tests PublicationFixture

def main (args : List String) : IO Unit := do
  let t ← Checks.new
  let dir := args.headD "out/empty-jobs/runtime"
  IO.FS.createDirAll dir
  for name in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    let path := dir ++ "/" ++ name
    if ← System.FilePath.pathExists path then IO.FS.removeFile path
  let sm ← Sim.new
  let s ← App.start sm.io #[640, 900, 0, 0, 160] (dir ++ "/quiet.db")
  s.wr.setPaused true
  let query : Reader.RM (Community.Write × Array Data.Q) :=
    readView (Community.unwrap "missing-community".toUTF8) #[]
  let ((nothing, _), _) ← query.run { rd := s.rd }
  t.ok "actual maintenance view returns an empty write without a node key" nothing.ops.isEmpty
  let before ← s.wr.busy.get
  for _ in [:100] do s.wr.submit ⟨nothing.ops, false⟩
  let jobs ← s.wr.jobs.get
  IO.println s!"empty writer jobs: busy={← s.wr.busy.get}, queued={jobs.writes.length + jobs.events.length}"
  t.ok "empty maintenance writes do not occupy either real writer FIFO" jobs.isEmpty
  t.ok "empty maintenance writes do not inflate real writer busy accounting" ((← s.wr.busy.get) == before)
  let (_, parked) ← (show App.M Unit from do
    for _ in [:100] do App.submit ⟨nothing.ops, true⟩).run { s with active := false }
  IO.println s!"empty parked jobs: queued={parked.toNode.size}, pendingOpBytes={parked.queuedWrites.length}"
  t.ok "empty writes do not accumulate parked jobs while the app is inactive" parked.toNode.isEmpty
  t.ok "empty writes do not consume pending-op budget" parked.queuedWrites.isEmpty
  -- A positive control uses the same production submit/turn with real signed
  -- bytes and checks actual SQLite; suppressing every job cannot pass.
  let w ← writer
  let op := root "nonempty job must still commit"
  w.submit ⟨[op], true⟩
  t.ok "nonempty signed submission retains its actual writer ownership" ((← w.busy.get) == 1)
  discard <| w.turn s.rd Lifecycle.save
  t.ok "nonempty signed submission still commits a valid SQLite op" (← valid s.rd op)
  t.ok "nonempty selected job balances actual busy accounting"
    ((← w.busy.get) == 0 && (← w.jobs.get).isEmpty && (← w.count.get) == 1)
  let (_, kept) ← (App.submit ⟨[op], true⟩).run { s with active := false }
  t.ok "nonempty parked write retains its original batch" (kept.toNode == #[[op]])
  t.ok "nonempty parked write retains its recovery journal" (kept.queuedWrites == [op.bytes])
  let code ← t.finish "empty-jobs"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
