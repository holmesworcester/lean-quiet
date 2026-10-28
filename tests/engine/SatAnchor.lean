/-
The conversation's window and counts about a saturated anchor, as the
reader reads them (Reader.eval), on SQLite.

A device founds a community and posts below the counter cap; a member's
post claims a huge counter (saturating the channel) and more posts
follow past the cap, each listed by this device's receipt of it. The
anchor is a saturated message, then (as a control) one below the cap.
For each:
- the counts beside it (`Want.count`) are the messages newer than it
  and the rest, the anchor among them: newer + older = all;
- the window about it (`Want.window`) holds it.
-/
import tests.engine.Lib
import ops.app.Reader

open Engine Community Tests

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/sat_anchor"
  IO.FS.createDirAll dir
  let t ← Checks.new
  let path := dir ++ "/a.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  let seed := sha256 "device A".toUTF8
  let d := Device.ofSeed seed
  -- the app's store: the node's family, its views read through the reader
  let mine (w : Write) : IO Unit := (receive Data.fam (intake Data.fam true w.ops)).run db
  let viewOn {α : Type} (v : View Fact α) : IO α := do
    let ((a, _), _) ← (Data.readView v #[] : Reader.RM _).run { rd := db }
    pure a
  let sendOn (v : View Fact Write) : IO Write := viewOn v
  let receipts (ops : List Op) : IO (List Op) := do
    let mut out := []
    for o in ops do out := out ++ (← viewOn (receiptFor o))
    return out
  let nonceOf (tag : String) : ByteArray := (sha256 tag.toUTF8).extract 0 24
  let k := sha256 "Acme's content key".toUTF8
  mine (found seed "Acme".toUTF8 "Ann".toUTF8 1 k (sha256 "esk 1".toUTF8))
  let c := (root d).id
  let mins := 29350000
  -- below the cap
  for i in [0:6] do
    mine (← sendOn (send c c d k (nonceOf s!"low {i}") s!"low {i}".toUTF8 (mins + i)))
  -- a huge counter saturates the channel; past it, every post is listed
  -- by its receipt
  let huge := sealedPost c c d k (nonceOf "huge") "MAX".toUTF8 (2 ^ 200) (mins + 100)
  mine ⟨[huge]⟩
  mine ⟨← receipts [huge]⟩
  for i in [0:4] do
    mine (← sendOn (send c c d k (nonceOf s!"high {i}") s!"high {i}".toUTF8 (mins + 200 + i)))
  -- the conversation, newest first, as the store lists it
  let all ← viewOn (readable c (limit := none))
  let ids := all.rows.map (·.1)
  t.ok s!"the conversation lists every message once ({ids.length})" (ids.length == 11 && ids.eraseDups.length == 11)
  let st : Reader.St := { rd := db }
  let check (what : String) (p : Pos) : IO Unit := do
    let some i := ids.findIdx? (· == p) | t.ok s!"{what}: the anchor is listed" false
    -- counts
    let ((v, _), _) ← (Reader.eval (.count c (some p))).run st
    match v with
    | .count newer older =>
      t.ok s!"{what}: the counts are the messages newer than it ({newer}) and the rest ({older}), the anchor among them"
        (newer == i && older == ids.length - i && newer + older == ids.length)
    | _ => t.ok s!"{what}: the counts are read" false
    -- the window about it
    let ((w, _), _) ← (Reader.eval (.window c (some p) 100 100)).run st
    match w with
    | .window wids _ =>
      t.ok s!"{what}: the window about it holds it, and every message ({wids.size})"
        (wids.contains p && wids.size == ids.length)
    | _ => t.ok s!"{what}: the window is read" false
  -- a saturated anchor: the huge one, with posts past the cap above it
  match all.rows.find? (·.1.2 == huge.id) with
  | some (p, _) => check "a saturated anchor" p
  | none => t.ok "the saturated message is listed" false
  -- the control: an anchor below the cap
  match ids[ids.length - 3]? with
  | some p => check "an anchor below the cap" p
  | none => t.ok "a message below the cap is listed" false
  t.finish "sat_anchor"
