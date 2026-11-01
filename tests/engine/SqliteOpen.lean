import tests.engine.Lib

open Engine Tests

namespace SqliteOpen

def waitDone {α : Type} (task : Task α) (ms : Nat) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← IO.hasFinished task then return true
    IO.sleep 2
  return ← IO.hasFinished task

def resetDb (path : String) : IO Unit := do
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)

def run (t : Checks) : IO Unit := do
  IO.FS.createDirAll "out/catalog-retry/sqlite-open"
  let path := "out/catalog-retry/sqlite-open/initialized.db"
  resetDb path
  let owner ← Db.openAt path
  owner.exec "BEGIN IMMEDIATE"
  let reader ← IO.asTask (prio := .dedicated) do
    let db ← Db.openAt path
    return !(← db.query "SELECT version FROM catalog_version WHERE version = 1" #[]).isEmpty
  let finished ← waitDone reader 250
  t.ok "initialized database opens without acquiring the held writer lock" finished
  owner.exec "ROLLBACK"
  let .ok opened ← IO.wait reader | throw (IO.userError "opening initialized database failed")
  t.ok "initialized database retains its catalog version" opened
  let legacy := "out/catalog-retry/sqlite-open/concurrent-legacy.db"
  resetDb legacy
  let db ← Db.open legacy
  db.exec "PRAGMA journal_mode=WAL; CREATE TABLE ops (id BLOB PRIMARY KEY, bytes BLOB NOT NULL) WITHOUT ROWID; INSERT INTO ops VALUES (x'01',x'02')"
  let ready ← IO.Promise.new
  let openOnce := do
    discard <| IO.wait ready.result?
    let db ← Db.openAt legacy
    return (← db.query "SELECT CAST(seq AS TEXT), id FROM catalog" #[])
  let a ← IO.asTask (prio := .dedicated) openOnce
  let b ← IO.asTask (prio := .dedicated) openOnce
  ready.resolve ()
  let doneA ← waitDone a 3000
  let doneB ← waitDone b 3000
  t.ok "concurrent first opens both complete catalog migration" (doneA && doneB)
  let .ok rowsA ← IO.wait a | throw (IO.userError "first migration failed")
  let .ok rowsB ← IO.wait b | throw (IO.userError "concurrent migration failed")
  t.ok "concurrent migration backfills one stable catalog position" (rowsA == #[#["1".toUTF8, ⟨#[1]⟩]] && rowsB == rowsA)

end SqliteOpen
