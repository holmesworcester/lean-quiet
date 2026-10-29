/- The actual root → child collection → message tree over signed SQLite
ops. A deliberately large clump is windowed; it is never a paint unit. -/
import platforms.headless.Sim
import tests.engine.Checks

open App Engine Community Data Tests

namespace ClumpLists

def settle (n : Nat := 40) : M Unit := do
  for _ in [0:n] do
    steps 1
    IO.sleep 2

def run (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let db := dir ++ "/quiet.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (db ++ suffix) then IO.FS.removeFile (db ++ suffix)
  let sm ← Sim.new
  sm.viewport.set #[390, 844, 0, 0, 160]
  let initial ← App.start sm.io (← sm.viewport.get) db
  let (_, final) ← (show M Unit from do
    found "Clump windows" "Alice"
    let s ← get
    let some key ← intentView (Community.currentKey s.me.c) | throw (IO.userError "fixture key missing")
    let root := sealedPost s.me.c s.me.adm s.me.dev key (← newBytes 24) "Root header".toUTF8 1 100
    let mut ops := [root]
    for i in [0:340] do
      let child := sealedPost s.me.c s.me.adm s.me.dev key (← newBytes 24)
        s!"Child {i}: its own message op and paint.".toUTF8 (i + 2) 101 (some root.id)
      ops := ops ++ [child]
    let last := sealedPost s.me.c s.me.adm s.me.dev key (← newBytes 24) "A later root".toUTF8 500 110
    ck.ok "signed large-clump fixture is accepted" (← writeAll ⟨ops ++ [last]⟩)
    openPage .chat
    waitIdle sm
    settle
    let s ← get
    ck.ok "outer collection contains roots only and total still counts messages"
      (s.roots.size == 2 && s.total == 342 && s.roots.all (fun p => p.2 == root.id || p.2 == last.id))
    let group := s.clumps.getD root.id {}
    ck.ok "a 340-child group holds a bounded child page and counted older spacer"
      (group.ready && group.ids.size ≤ 2 * half && group.older > 0 && group.ids.size + group.newer + group.older == 340)
    ck.ok "projection geometry exactly equals the sum of its flat cells"
      ((ClumpList.cells (ByteArray.empty, root.id) group (heightOf s) est).foldl (fun n cell => n + cell.2.1) 0 ==
        ClumpList.extent (ByteArray.empty, root.id) group (heightOf s) est)
    ck.ok "spacers never mount message ops or own queries"
      (s.spacers.toList.all fun id => !s.rows.contains id &&
        !s.queryNeeds.toList.any (fun n => n.key == .row s.me.c s.me.adm id))
    let gap := ClumpList.gap root.id 1
    let restoredGap := applyCheckpoint s (checkpoint { s with mark := some (gap, 19) })
    ck.ok "checkpointing an unloaded range restores a real root, never a synthetic op"
      (s.spacers.contains gap && restoredGap.mark == some (root.id, 0) &&
       restoredGap.restorePos.map (·.2) == some root.id)
    ck.ok "continuations draw neither headers nor avatars and are shorter than roots"
      (s.rows.toList.any (fun (_, r) => r.data.clump == some root.id) &&
       s.rows.toList.all (fun (_, r) => r.data.clump.isNone ||
        (r.lay.name.isEmpty && r.lay.time.isEmpty && r.lay.textY == 0)))
    let plan ← s.sh.plan.get
    ck.ok "only the visible root owns the shared author query"
      ((plan.needs.filter (·.key == .author s.me.c s.me.user)).length == 1)
    let firstPage := group.ids
    -- A jump to the far edge must advance the child window without moving
    -- the root cursor or asking for an unbounded list.
    sm.b.set (← sm.maxB.get)
    settle 100
    let older ← get
    let olderGroup := older.clumps.getD root.id {}
    ck.ok "fast jump traverses the bounded child window to the old root"
      (olderGroup.older == 0 && olderGroup.ids != firstPage && older.rows.contains root.id)
    ck.ok "far-away child message queries retire independently of their root"
      (firstPage.any (fun p => !older.rows.contains p.2) && older.rows.size < 150)
    ck.ok "root header paints once, while children remain independent rows"
      ((older.rows[root.id]?).any (fun r => !r.lay.name.isEmpty && r.data.name == "Alice") &&
        older.rows.toList.any (fun (_, r) => r.data.clump.isSome && r.shown.isSome))
    let some (child, row) := older.rows.toList.find? (fun (_, r) => r.data.clump.isSome)
      | throw (IO.userError "visible continuation missing")
    sm.b.set ((rowBottom older child).getD 0 + row.lay.h / 2).toFloat
    settle
    let saved ← get
    let mark := captureAnchor saved
    let cp := checkpoint { saved with mark := mark }
    ck.ok "a child checkpoint records both its root cursor and its own position"
      (mark.isSome && ((applyCheckpoint saved cp).anchor.map (·.2) == some root.id) &&
       (applyCheckpoint saved cp).restorePos.map (·.2) == mark.map (·.1))
    openPage .home
    steps 3
    modify fun state => applyCheckpoint { state with
      roots := #[], ids := #[], clumps := {}, clumpHeights := {}, cellRoot := {}, spacers := {}, heights := {} } cp
    sm.b.set 0
    settle 100
    ck.ok "a cold child collection restores the same message and top-edge offset"
      (captureAnchor (← get) == mark && !(← get).restoreAnchor)
    sm.b.set 0
    settle 100
    let newest ← get
    ck.ok "returning to the newest page restores both collections"
      (newest.rows.contains last.id && (newest.clumps.getD root.id {}).newer == 0)
    openPage .home
    steps 4
    let plan ← (← get).sh.plan.get
    ck.ok "leaving chat releases all root and child collection queries"
      (plan.needs.all fun n => match n.key with
        | .clumps .. | .clumpCount .. | .row .. => false
        | _ => true)
    ).run initial
  final.raster.reconcile []

end ClumpLists

def main (args : List String) : IO Unit := do
  let ck ← Checks.new
  ClumpLists.run (args.headD "out/clump-lists") ck
  let code ← ck.finish "clump-lists"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
