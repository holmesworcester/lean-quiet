/-
The SQLite behind the actual Db externs has the shipped version and
options, and preserves blob parameters. A store opened as the app opens
it (`Db.openAt`, which `Data.openDb` and the node's connection both
call) is in WAL mode and syncs every commit to storage
(`synchronous = FULL`), so a committed write turn survives power loss;
a connection set to NORMAL fails that check. These are native checks,
not laws.
-/
import engine.core.Sqlite

open Engine

/-- What `PRAGMA name` answers on db, as text. -/
def pragma (db : Db) (name : String) : IO (List String) := do
  return (col0 (← db.query s!"PRAGMA {name}" #[])).filterMap String.fromUTF8?

/-- db syncs each commit to storage before the commit returns: in WAL
mode, `synchronous` is FULL (2). NORMAL (1) syncs only at checkpoints,
so power loss can undo the last commits. -/
def syncsCommits (db : Db) : IO Bool := do
  return (← pragma db "journal_mode") == ["wal"] && (← pragma db "synchronous") == ["2"]

def main (args : List String) : IO UInt32 := do
  let db ← Db.open ":memory:"
  let mut passed := 0
  let mut failed := 0
  let version ← db.query "SELECT sqlite_version()" #[]
  let options ← db.query "PRAGMA compile_options" #[]
  let opts := (col0 options).filterMap String.fromUTF8?
  IO.println s!"SQLite {version}; options {opts}"
  let blob := ByteArray.mk #[0, 255, 39, 0, 128]
  let rows ← db.query "SELECT ?" #[blob]
  let dqsOff ← try
    let _ ← db.query "SELECT \"not_a_column\"" #[]
    pure false
  catch _ => pure true
  -- A store on disk, opened as the app opens it; a second connection to
  -- it (the node's, a reader's); and a third, set back to NORMAL.
  let dir := args.headD "out/sqlite-build"
  IO.FS.createDirAll dir
  let path := dir ++ "/store.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let store ← Db.openAt path
  let other ← Db.openAt path
  let normal ← Db.openAt path
  normal.exec "PRAGMA synchronous = NORMAL"
  for (name, ok) in [
      ("version 3.50.4", (col0 version).filterMap String.fromUTF8? == ["3.50.4"]),
      ("THREADSAFE=2", opts.contains "THREADSAFE=2"),
      ("DQS=0", opts.contains "DQS=0"),
      ("DEFAULT_MEMSTATUS=0", opts.contains "DEFAULT_MEMSTATUS=0"),
      ("OMIT_LOAD_EXTENSION", opts.contains "OMIT_LOAD_EXTENSION"),
      ("double quotes name columns, not strings", dqsOff),
      ("blob bytes including NUL survive the shared glue", rows == #[#[blob]]),
      ("a store opened as the app opens it syncs each commit (WAL, synchronous FULL)",
        ← syncsCommits store),
      ("so does a second connection to it", ← syncsCommits other),
      ("control: a connection set to synchronous NORMAL fails that check",
        !(← syncsCommits normal))] do
    if ok then passed := passed + 1
    else failed := failed + 1; IO.eprintln s!"FAIL: {name}"
  IO.println s!"sqlite build: {passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
