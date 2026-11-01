/- Force the actual Writer.commitSave acknowledgement to overlap a reader.
The callback commits a real lifecycle checkpoint first, then gates only its
return. GDB pauses the actual saved-ref getter while commitSave publishes. -/
import app.Screen

open Engine Data

@[extern "lq_stop_probe_arm_ref"] opaque armSaved (ref : @& IO.Ref Nat) : IO Unit
@[extern "lq_stop_probe_wait"] opaque waitRelease : IO Unit
@[extern "lq_stop_probe_entered"] opaque entered : IO Unit
@[extern "lq_stop_probe_done"] opaque done : IO Unit
@[extern "lq_stop_probe_injected"] opaque injected : IO Bool

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/checkpoint-ack/data"
  IO.FS.createDirAll dir
  let path := dir ++ "/checkpoint.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  Lifecycle.init db
  let checkpoint : Lifecycle.Checkpoint :=
    (1, 1, "accepted-user".toUTF8, "visible-message".toUTF8, 27,
      [Codec.encode ["draft that survives suspension".toUTF8], "community".toUTF8])
  let writer : Writer := ⟨← IO.mkRef WriterQueue.empty, ← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef false,
    ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef (0, none), ← IO.mkRef 0⟩
  writer.save (Codec.encode checkpoint)
  let committed ← IO.Promise.new
  let job ← IO.asTask (prio := .dedicated) do
    writer.commitSave db fun db payload => do
      Lifecycle.save db payload
      committed.resolve ()
      waitRelease
      entered
    done
  discard <| IO.wait committed.result?
  armSaved writer.saved
  let before ← writer.saveDone
  let result ← IO.wait job
  let after ← writer.saveDone
  let (requested, queued) ← writer.saving.get
  let saved ← writer.saved.get
  let observed ← Lifecycle.load (← Db.openAt path)
  -- Once saving has been consumed, another actual loop pass cannot repair a
  -- lost acknowledgement by silently committing the checkpoint again.
  writer.commitSave db Lifecycle.save
  let retried ← writer.saveDone
  let rows ← db.query "SELECT bytes FROM app_ops" #[]
  let durable := observed == some checkpoint && rows.size == 1
  if !(← injected) || !result.isOk || before || !durable || queued.isSome ||
      requested != 1 || saved != 1 || !after || !retried then
    IO.eprintln s!"FAIL: committed checkpoint remains acknowledged after the overlapping old read (durable={durable}, queued={queued.isSome}, saved={saved}, requested={requested}, before={before}, after={after}, retry={retried})"
    return 1
  let next : Lifecycle.Checkpoint := (1, 0, "accepted-user".toUTF8, .empty, 0, ["newer draft".toUTF8])
  writer.save (Codec.encode next)
  writer.commitSave db Lifecycle.save
  unless (← writer.saveDone) && (← Lifecycle.load (← Db.openAt path)) == some next do
    IO.eprintln "FAIL: a later actual checkpoint is stored and acknowledged"
    return 1
  IO.println "checkpoint-ack: actual SQLite checkpoint and completion survive SDK overlap; later checkpoint passes"
  return 0
