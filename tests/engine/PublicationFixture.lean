import ops.app.Reader
import ops.app.Lifecycle

open Engine Data
namespace PublicationFixture

@[extern "lq_stop_probe_arm_ref"] opaque armNat (ref : @& IO.Ref Nat) : IO Unit
@[extern "lq_stop_probe_arm_ref"] opaque armBool (ref : @& IO.Ref Bool) : IO Unit
@[extern "lq_stop_probe_wait"] opaque waitRelease : IO Unit
@[extern "lq_stop_probe_entered"] opaque entered : IO Unit
@[extern "lq_stop_probe_done"] opaque done : IO Unit
@[extern "lq_stop_probe_injected"] opaque injected : IO Bool

def writer (paused : Bool := false) : IO Writer :=
  return ⟨← IO.mkRef WriterQueue.empty, ← IO.mkRef 0, ← IO.mkRef #[], ← IO.mkRef paused,
    ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef (0, none), ← IO.mkRef 0⟩

def root (name : String) : Op :=
  Community.root (Community.Device.named name) (Connection.sodium.suite.pub (sha256 name.toUTF8))

def database (dir : String) : IO (String × Db) := do
  IO.FS.createDirAll dir
  let path := dir ++ "/publication.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  db.filings
  Lifecycle.init db
  return (path, db)

def valid (db : Db) (op : Op) : IO Bool := do
  let status ← (Store.getStatus op.id : SqlM SF _).run db
  return match status with | some (.valid _) => true | _ => false

def waitFor (ms : Nat) (ready : IO Bool) : IO Bool := do
  let end_ := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < end_ do
    if ← ready then return true
    IO.sleep 1
  return false
end PublicationFixture
