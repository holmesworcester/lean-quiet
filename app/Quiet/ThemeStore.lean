/-
Device preference storage, separate from community ops and their sync.
The representation is Theme.encode/decode. SQLite durability is tested
by restarting a process, not assumed by the pure round-trip law.
-/
import Quiet.Theme
import Engine.Sqlite

namespace Theme

def load (db : Engine.Db) : IO Setting := do
  db.exec "CREATE TABLE IF NOT EXISTS appearance (id INTEGER PRIMARY KEY CHECK(id = 1), value BLOB NOT NULL)"
  let rows ← db.query "SELECT value FROM appearance WHERE id = 1" #[]
  return decode (String.fromUTF8! ((rows[0]? >>= (·[0]?)).getD .empty))

def save (db : Engine.Db) (setting : Setting) : IO Unit := do
  let _ ← db.query "INSERT OR REPLACE INTO appearance (id, value) VALUES (1, ?)" #[(encode setting).toUTF8]

end Theme
