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
      let mut queued := (s.conn.onWant {} ix ids).conn
      while !queued.owed.isEmpty do
        let (rest, urgent, bulk) ← (queued.serveOwed fam {} 131072 [] : SqlM F _).run db
        queued := rest
        sent := sent ++ urgent ++ bulk
  return sent

end Tests
