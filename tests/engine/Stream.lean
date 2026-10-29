/-
SQLite test transfers through the connection's filed advertisements and
authorized want handler. No separate model of what may leave a node.
-/
import ops.sync.Conn
import engine.core.Sqlite

namespace Tests
open Engine Sync

def streamOps {F : Type} [Codec F] [SortKey F] (fam : Family F) (db : Db) : IO (List Op) := do
  let all ← (dumpOps (F := F)).run db
  let c := (Conn.open false (all.filterMap fam.room).eraseDups 0 0).conn
  let ix := Index.ofOps fam all
  let s ← (c.filed fam {} (all.map Op.id) : SqlM F Step).run db
  let mut sent := []
  for msg in s.send do
    if let some (.hold _ ids) := Msg.ofOp msg then
      let reply ← (s.conn.onWant fam {} ix ids : SqlM F Step).run db
      sent := sent ++ reply.send
  return sent

end Tests
