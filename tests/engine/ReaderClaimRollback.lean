/- Actual Reader/SQLite batch ownership through failed transaction setup,
query rollback, concurrent admission and cancellation. The schema fault is
explicit test injection, not a claim that ordinary app code renames tables. -/
import app.Screen
import tests.engine.Checks

open Engine Community Data Tests

namespace ReaderClaimRollback

def founding : Reader.RM Community.Write := do
  return (← readView (Community.found (sha256 "claim device".toUTF8)
    "Claim rollback".toUTF8 "Ann".toUTF8 1 (sha256 "claim key".toUTF8)
    (sha256 "claim wrap".toUTF8) (sha256 "claim node".toUTF8)) #[]).1

def exercise (ck : Checks) (fault : Bool) : IO Unit := do
  let tag := if fault then "fault" else "healthy"
  let dir := "out/reader-claim/runtime"
  IO.FS.createDirAll dir
  let path := dir ++ "/" ++ tag ++ ".db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  db.filings
  let rd ← Db.openAt path
  let sh ← Reader.Shared.new (← IO.mkRef 0)
  let calls ← IO.mkRef 0
  let id := ("claim-" ++ tag).toUTF8
  sh.act id (do calls.modify (· + 1); founding)
  sh.notes.modify (·.push ⟨"claim-note".toUTF8, ("position".toUTF8, "note-id".toUTF8), true⟩)
  ck.ok s!"{tag}: actual founding intent is accepted exactly once" ((← sh.acts.get).size == 1 && (← sh.done.get).isEmpty)
  if fault then db.exec "ALTER TABLE filings RENAME TO hidden_filings"
  let initial : Reader.St := { rd }
  let (error, retained) ← try
      let (_, next) ← (Reader.pass sh).run initial
      pure ("", next)
    catch e => pure (toString e, initial)
  if fault then db.exec "ALTER TABLE hidden_filings RENAME TO filings"
  ck.ok s!"{tag}: selected fault is actual SQLite journal failure"
    (if fault then error.contains "no such table: filings" else error.isEmpty)
  let queued := (← sh.acts.get).size
  let done := (← sh.done.get).size
  let notes := (← sh.notes.get).size
  ck.ok s!"{tag}: every accepted action still has exactly one owner or result" (queued + done == 1)
  if fault then
    ck.ok "fault: unprocessed notice remains available after journal rollback" (notes == 1)
  let mut state := retained
  for _ in [0:3] do
    let (_, next) ← (Reader.pass sh).run state
    state := next
  let results ← sh.done.get
  ck.ok s!"{tag}: healthy retry invokes accepted intent exactly once" ((← calls.get) == 1)
  ck.ok s!"{tag}: healthy retry reports exactly one judged founding write"
    (results.size == 1 && results[0]?.any (fun p => p.1 == id && p.2.isSome) && !(← sh.out.get).isEmpty)
  IO.println s!"reader-claim trace: {tag}, error={error}, queuedAfter={queued}, doneAfter={done}, notesAfter={notes}, invocations={← calls.get}, finalDone={results.size}, pending={(← sh.out.get).size}"

def openPair (tag : String) : IO (Db × Db) := do
  let path := "out/reader-claim/runtime/" ++ tag ++ ".db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  db.filings
  return (db, ← Db.openAt path)

def lateArrival (ck : Checks) : IO Unit := do
  let (db, rd) ← openPair "late"
  db.exec "CREATE TABLE claim_snapshot (value TEXT)"
  db.exec "INSERT INTO claim_snapshot VALUES ('old')"
  let sh ← Reader.Shared.new (← IO.mkRef 0)
  let observed ← IO.mkRef (#[] : Array String)
  let readSnapshot : Reader.RM Unit := do
    let rows ← (← get).rd.query "SELECT value FROM claim_snapshot" #[]
    let value := rows[0]?.bind (·[0]?) |>.bind String.fromUTF8? |>.getD "missing"
    observed.modify (·.push value)
  sh.act "first".toUTF8 (do readSnapshot; founding)
  sh.notes.modify (·.push ⟨"before".toUTF8, ("position".toUTF8, "first".toUTF8), true⟩)
  let (_, next) ← (Reader.pass sh (afterJournal := do
    -- The actual reader transaction has established its SQL snapshot.
    db.exec "UPDATE claim_snapshot SET value = 'new'"
    sh.act "late".toUTF8 (do readSnapshot; return ⟨[]⟩)
    sh.notes.modify (·.push ⟨"late".toUTF8, ("position".toUTF8, "late".toUTF8), true⟩))).run { rd }
  ck.ok "late: captured action reads the original actual SQLite snapshot" ((← observed.get) == #["old"])
  ck.ok "late: newly appended action retains its own next-pass owner"
    ((← sh.acts.get).map (·.1) == #["late".toUTF8] && (← sh.done.get).size == 1)
  ck.ok "late: only original note prefix is acknowledged despite generated act notices" ((← sh.notes.get).size == 1)
  discard <| (Reader.pass sh).run next
  ck.ok "late: next action reads the newer actual SQLite snapshot exactly once" ((← observed.get) == #["old", "new"])
  ck.ok "late: both actions finish and both original notes are consumed"
    ((← sh.acts.get).isEmpty && (← sh.notes.get).isEmpty && (← sh.done.get).size == 2)

def cancelled (ck : Checks) : IO Unit := do
  let (_, rd) ← openPair "cancelled"
  let commits ← IO.mkRef 0
  let old ← Reader.Shared.new commits
  let enabled ← IO.mkRef true
  let calls ← IO.mkRef 0
  old.act "retired".toUTF8 (do calls.modify (· + 1); founding)
  old.notes.modify (·.push ⟨"retired".toUTF8, ("position".toUTF8, "retired".toUTF8), true⟩)
  discard <| (Reader.pass old (afterJournal := enabled.modify (fun _ => false))).run
    { rd, enabled := enabled.get }
  ck.ok "cancel: revoked snapshot executes no intent or completion" ((← calls.get) == 0 && (← old.done.get).isEmpty)
  -- This succeeds only if the early-return path closed the old transaction.
  let closed ← try
      rd.exec "BEGIN"
      rd.exec "COMMIT"
      pure true
    catch _ => do
      rd.exec "ROLLBACK"
      pure false
  ck.ok "cancel: early return leaves no open SQLite transaction" closed
  ck.ok "cancel: reader has not claimed the revoked captured batch" ((← old.acts.get).size == 1 && (← old.notes.get).size == 1)
  -- Teardown discards the detached batches and uses a new Shared. Do not
  -- reuse the old reader's queue or invent a reactivation contract for it.
  old.acts.set #[]
  old.notes.set #[]
  let fresh ← Reader.Shared.new commits
  fresh.act "replacement".toUTF8 (do calls.modify (· + 1); founding)
  discard <| (Reader.pass fresh).run { rd }
  ck.ok "cancel: replacement lifetime runs only its own accepted action"
    ((← calls.get) == 1 && (← fresh.done.get).size == 1 && (← old.done.get).isEmpty)

def noteRollback (ck : Checks) : IO Unit := do
  let (_, rd) ← openPair "notes"
  let (w, _) ← founding.run { rd }
  let some pending ← Reader.judgeWrite rd #[] w | throw (IO.userError "founding unexpectedly refused")
  let some c := pending.findSome? (fun p => match p.fact with
    | .admission c _ _ _ => some c
    | _ => none) | throw (IO.userError "founding has no admission")
  let sh ← Reader.Shared.new (← IO.mkRef 0)
  let want := Reader.Want.people c
  sh.setWants #[want]
  let (_, retained) ← (Reader.pass sh).run { rd }
  let count : IO (Option Nat) := do
    return match (← sh.board.get).get? want with
      | some (.people n _, _) => some n
      | _ => none
  ck.ok "notes: actual count starts empty" ((← count) == some 0)
  sh.out.modify (· ++ pending)
  let filings := Pending.filings pending.toList
  sh.notes.modify (· ++ filings)
  let queries ← IO.mkRef 0
  let failed ← try
      discard <| (Reader.pass sh).run { retained with afterQuery := fun _ => do
        queries.modify (· + 1)
        throw (IO.userError "injected failure after pending query") }
      pure false
    catch _ => pure true
  ck.ok "notes: real pending query fails before COMMIT" (failed && (← queries.get) == 1)
  ck.ok "notes: query failure retains the captured local notices" ((← sh.notes.get).size == filings.size)
  discard <| (Reader.pass sh).run retained
  ck.ok "notes: healthy retry refreshes cached count from pending founding" ((← count) == some 1)
  ck.ok "notes: successful COMMIT finally consumes the captured notices" ((← sh.notes.get).isEmpty)

def beginFailure (ck : Checks) : IO Unit := do
  let (_, rd) ← openPair "begin"
  let sh ← Reader.Shared.new (← IO.mkRef 0)
  let calls ← IO.mkRef 0
  sh.act "begin".toUTF8 (do calls.modify (· + 1); founding)
  sh.notes.modify (·.push ⟨"begin".toUTF8, ("position".toUTF8, "begin".toUTF8), true⟩)
  rd.exec "BEGIN"
  let error ← try
      discard <| (Reader.pass sh).run { rd }
      pure ""
    catch e => pure (toString e)
  rd.exec "ROLLBACK"
  ck.ok "begin: actual SQLite BEGIN failure is injected" (error.contains "within a transaction")
  ck.ok "begin: failed transaction startup preserves accepted action and note"
    ((← sh.acts.get).size == 1 && (← sh.notes.get).size == 1 && (← sh.done.get).isEmpty)
  discard <| (Reader.pass sh).run { rd }
  ck.ok "begin: healthy retry invokes retained intent once" ((← calls.get) == 1)
  ck.ok "begin: healthy retry produces a judged completion"
    ((← sh.done.get).size == 1 && !(← sh.out.get).isEmpty)

end ReaderClaimRollback

def main : IO UInt32 := do
  let ck ← Checks.new
  ReaderClaimRollback.exercise ck false
  ReaderClaimRollback.exercise ck true
  ReaderClaimRollback.lateArrival ck
  ReaderClaimRollback.cancelled ck
  ReaderClaimRollback.noteRollback ck
  ReaderClaimRollback.beginFailure ck
  ck.finish "reader_claim_rollback"
