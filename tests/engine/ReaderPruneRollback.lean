/- Actual SQLite query-cache rollback and the production journal pruner.
Admission facts seed the same member-count fixture used by component tests;
this checks notice lifetime, not signature/admission validation. -/
import app.Screen
import tests.engine.Checks

open Engine Community Data Tests
namespace ReaderPruneRollback

def writer : IO Writer :=
  return ⟨← IO.mkRef WriterQueue.empty, ← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef false,
    ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef (0, none), ← IO.mkRef 0⟩

def member (db : Db) (w : Writer) (c : Id) (i : Nat) : IO Unit := do
  let f : SF := .inl (.admission c s!"user-{i}".toUTF8 s!"device-{i}".toUTF8 s!"node-{i}".toUTF8 .empty)
  db.exec "BEGIN"
  (show SqlM SF Unit from do
    Store.setStatus s!"admission-{i}".toUTF8 (.valid f)
    for k in fam.keys f do Store.index k s!"admission-{i}".toUTF8).run db
  db.exec "COMMIT"
  -- The production node's notify callback publishes this commit count.
  w.count.modify (· + 1)

def count (sh : Reader.Shared) (want : Reader.Want) : IO (Option Nat) := do
  return match (← sh.board.get).get? want with
    | some (.people n _, _) => some n
    | _ => none

end ReaderPruneRollback
open ReaderPruneRollback

def main : IO UInt32 := do
  let ck ← Checks.new
  let dir := "out/reader-prune/runtime"
  IO.FS.createDirAll dir
  let path := dir ++ "/reader.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  db.filings
  let rd ← Db.openAt path
  let ui ← Db.openAt path
  let prune ← Db.openAt path
  let wr ← writer
  let c := "real-reader-prune-rollback".toUTF8
  for i in [0:40] do member db wr c i
  let sh ← Reader.Shared.new wr.count
  let want := Reader.Want.people c
  sh.setWants #[want]
  let (_, retained) ← (Reader.pass sh).run { rd }
  let warm ← count sh want
  ck.ok "actual reader warms a 40-member SQLite count" (warm == some 40)
  let oldSeen ← sh.seen.get
  ck.ok "successful warm pass acknowledges its retained cursor" (oldSeen == retained.seen && oldSeen > 0)
  member db wr c 40
  let (newFilings, _, newTop) ← db.filingsSince retained.seen
  ck.ok "the 41st committed member produces real dependency filings" (!newFilings.isEmpty && newTop > retained.seen)
  let queries ← IO.mkRef 0
  let fault : Reader.St := { retained with afterQuery := fun _ => do
    queries.modify (· + 1)
    throw (IO.userError "injected failure after actual member-count query") }
  let failed ← try
      discard <| (Reader.pass sh).run fault
      pure false
    catch _ => pure true
  ck.ok "actual recalculation throws and rolls back before returning reader state" (failed && (← queries.get) == 1)
  let premature ← sh.seen.get
  ck.ok "failed transaction does not acknowledge unretained reader progress" (premature == retained.seen)
  -- This is the frame's actual journal snapshot and its min acknowledgement.
  ui.exec "BEGIN"
  let (_, _, uiTop) ← ui.filingsSince 0
  ui.exec "COMMIT"
  wr.noticed (min uiTop (← sh.seen.get))
  wr.pruneOnce prune
  let (remaining, _, _) ← db.filingsSince retained.seen
  ck.ok "actual pruner retains the notice needed by the failed reader" (!remaining.isEmpty)
  let (direct, _) ← (Reader.evalLogged want).run { rd := ← Db.openAt path }
  ck.ok "underlying SQLite still has 41 members after pruning" (direct == .people 41 true)
  -- Reader.work retains this exact old St when pass throws.
  let (_, healthy) ← (Reader.pass sh).run retained
  let retried ← count sh want
  ck.ok "healthy reader retry after actual pruning refreshes the cached count to 41" (retried == some 41)
  wr.noticed (min uiTop (← sh.seen.get))
  wr.pruneOnce prune
  let (fs, vs, _) ← db.filingsSince 0
  ck.ok "successful retry permits journal pruning after the retained state advances"
    (healthy.seen == newTop && fs.isEmpty && vs.isEmpty)
  IO.println s!"reader-prune trace: warm={warm}, retained={retained.seen}, afterFailure={premature}, uiTop={uiTop}, remaining={remaining.size}, retry={retried}"
  return ← ck.finish "reader_prune_rollback"
