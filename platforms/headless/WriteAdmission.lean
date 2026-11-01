/- Actual send action and writer, with real signatures and SQLite. -/
import Quiet
import platforms.headless.Sim
import tests.engine.Checks

open App Engine Community Data

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/write-admission"
  IO.FS.createDirAll dir
  for name in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    let p := dir ++ "/" ++ name
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  let t ← Tests.Checks.new
  let s ← App.start sm.io #[1080, 2400, 128, 63, 420] (dir ++ "/quiet.db")
  let (_, s) ← (show M Unit from do
    sm.cmds.modify (·.push "found bounded writes|Ann")
    steps 4
    waitIdle sm
    openPage .chat
    steps 3).run s
  t.ok "real community and sender ready" (!s.me.c.isEmpty && !s.me.waiting)
  let before ← (dumpOps : SqlM SF _).run s.rd
  let huge := String.fromUTF8! (⟨Array.replicate (Sync.maxFrame + 1) 120⟩ : ByteArray)
  let (_, rejected) ← sendNow.run { s with text := huge }
  let after ← (dumpOps : SqlM SF _).run s.rd
  t.ok "oversized Send preserves the draft" (rejected.text == huge)
  t.ok "oversized Send reports failure" (rejected.toast.isSome)
  t.ok "oversized Send creates no optimistic or queued op"
    (rejected.out.size == s.out.size && rejected.queuedWrites == s.queuedWrites &&
      rejected.toNode.size == s.toNode.size && before.map Op.id == after.map Op.id)
  -- A saturated queue is represented by shared immutable buffers. No
  -- fabricated entries are submitted, journaled or passed to the writer.
  let lim : WriteAdmission.Limits := {}
  let countFull := List.replicate lim.ops ByteArray.empty
  let (_, countRejected) ← sendNow.run { s with text := "keep this count-limited draft", queuedWrites := countFull }
  t.ok "count exhaustion refuses without losing existing work or draft"
    (countRejected.text == "keep this count-limited draft" && countRejected.toast.isSome &&
      countRejected.queuedWrites == countFull && countRejected.out.size == s.out.size)
  let block : ByteArray := ⟨Array.replicate (1024 * 1024) 1⟩
  let byteFull := List.replicate (lim.bytes / block.size) block
  let (_, byteRejected) ← sendNow.run { s with text := "keep this byte-limited draft", queuedWrites := byteFull }
  t.ok "byte exhaustion refuses independently of count"
    (byteFull.length < lim.ops && byteRejected.text == "keep this byte-limited draft" &&
      byteRejected.toast.isSome && byteRejected.queuedWrites == byteFull && byteRejected.out.size == s.out.size)
  -- Check the boundary with a real signed operation, then let the same
  -- application action commit through its actual writer.
  let some k ← (intentView (Community.currentKey s.me.c)).run' s |
    throw (IO.userError "fixture has no community key")
  let w ← (intentView (Community.send s.me.c s.me.adm s.me.dev k (← App.newSized 24) "limit boundary".toUTF8 42)).run' s
  let size := WriteAdmission.bytes (w.ops.map Op.bytes)
  t.ok "exact count and byte boundary admits the signed batch"
    ((WriteAdmission.refusal ⟨w.ops.length, size⟩ [] w.ops).isNone)
  t.ok "one byte below the signed batch refuses"
    ((WriteAdmission.refusal ⟨w.ops.length, size - 1⟩ [] w.ops).isSome)
  s.wr.setPaused true
  let (_, accepted) ← sendNow.run { s with text := "accepted after pressure clears" }
  t.ok "successful Send clears draft and queues a fitting op"
    (accepted.text.isEmpty && accepted.out.size > s.out.size &&
      accepted.queuedWrites.length > s.queuedWrites.length &&
      (accepted.out.toList.map (·.op)).all WriteAdmission.fits)
  accepted.wr.setPaused false
  let (_, saved) ← (show M Unit from do waitIdle sm; steps 4).run accepted
  t.ok "accepted post commits and the queue releases capacity"
    (saved.total == s.total + 1 && saved.queuedWrites.isEmpty &&
      saved.rows.toList.any fun (_, row) => row.data.text == "accepted after pressure clears" && !row.data.pending)
  let code ← t.finish "app-write-admission"
  IO.Process.exit code.toUInt8
