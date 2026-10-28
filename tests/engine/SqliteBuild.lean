/-
The SQLite behind the actual Db externs has the shipped version and
options, and preserves blob parameters. These are native checks, not laws.
-/
import engine.core.Sqlite

open Engine

def main : IO UInt32 := do
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
  for (name, ok) in [
      ("version 3.50.4", (col0 version).filterMap String.fromUTF8? == ["3.50.4"]),
      ("THREADSAFE=2", opts.contains "THREADSAFE=2"),
      ("DQS=0", opts.contains "DQS=0"),
      ("DEFAULT_MEMSTATUS=0", opts.contains "DEFAULT_MEMSTATUS=0"),
      ("OMIT_LOAD_EXTENSION", opts.contains "OMIT_LOAD_EXTENSION"),
      ("double quotes name columns, not strings", dqsOff),
      ("blob bytes including NUL survive the shared glue", rows == #[#[blob]])] do
    if ok then passed := passed + 1
    else failed := failed + 1; IO.eprintln s!"FAIL: {name}"
  IO.println s!"sqlite build: {passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
