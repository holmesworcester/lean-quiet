/- Actual Writer.turn must not retry a failed lifecycle checkpoint ahead of
its already selected signed SQLite write. A missing real checkpoint table
causes the failure; the old recursive implementation is released after three
errors, so its negative control terminates without a timeout oracle. -/
import tests.engine.PublicationFixture
import tests.engine.Checks

open Engine Data Tests PublicationFixture

namespace WriterCheckpoint

def checkpoint (n : Nat) : Lifecycle.Checkpoint :=
  (1, n, "checkpoint-owner".toUTF8, "readable-message".toUTF8, n, [s!"draft-{n}".toUTF8])

def hideCheckpoint (db : Db) : IO Unit :=
  db.exec "ALTER TABLE app_ops RENAME TO checkpoint_unavailable"

def restoreCheckpoint (db : Db) : IO Unit :=
  db.exec "ALTER TABLE checkpoint_unavailable RENAME TO app_ops"

def oneAttempt (t : Checks) (dir : String) : IO Unit := do
  let (path, db) ← database (dir ++ "/failure")
  let observer ← Db.openAt path
  let w ← writer
  let op := root "signed write behind failing checkpoint"
  w.submit ⟨[op], true⟩
  w.save (Codec.encode (checkpoint 1))
  hideCheckpoint db
  let attempts ← IO.mkRef 0
  let failures ← IO.mkRef 0
  let restored ← IO.mkRef false
  let chosen ← w.turn db fun db bytes => do
    attempts.modify (· + 1)
    try Lifecycle.save db bytes
    catch e =>
      let failed ← failures.modifyGet fun n => (n + 1, n + 1)
      -- Only the broken recursive implementation reaches this recovery
      -- inside the first turn. It then returns normally on attempt four.
      if failed == 3 then
        restoreCheckpoint db
        restored.modify (fun _ => true)
      throw e
  let attempted ← attempts.get
  let failed ← failures.get
  let pending ← w.saving.get
  let saved ← w.saved.get
  let readable ← valid observer op
  let tables ← observer.query "SELECT name FROM sqlite_master WHERE type='table' AND name='app_ops'" #[]
  IO.println s!"checkpoint first turn: attempts={attempted}, SQL errors={failed}, selected={chosen.isSome}, readable={readable}, checkpointTable={ !tables.isEmpty }, pending={pending.2.isSome}, saved={saved}"
  t.ok "one actual writer turn attempts the failing checkpoint exactly once"
    (attempted == 1 && failed == 1)
  t.ok "selected signed write is committed and readable despite the checkpoint error"
    (chosen.any (fun j => j.ops.map (·.id) == [op.id]) && readable)
  t.ok "signed write is readable while the actual checkpoint table remains unavailable"
    (readable && tables.isEmpty)
  t.ok "failed checkpoint remains pending and unacknowledged after write service"
    (pending == (1, some (Codec.encode (checkpoint 1))) && saved == 0 && !(← w.saveDone))
  t.ok "checkpoint failure does not lose or double-count the selected job"
    ((← w.jobs.get).isEmpty && (← w.busy.get) == 0 && (← w.count.get) == 1)
  unless ← restored.get do restoreCheckpoint db
  let idle ← w.turn db Lifecycle.save
  t.ok "a later actual turn retries and acknowledges the retained checkpoint"
    (idle.isNone && (← w.saveDone) && (← Lifecycle.load observer) == some (checkpoint 1))
  t.ok "checkpoint recovery cannot repeat the already committed write"
    ((← w.count.get) == 1 && (← w.busy.get) == 0 && (← valid observer op))

def generations (t : Checks) (dir : String) : IO Unit := do
  let (path, db) ← database (dir ++ "/generations")
  let observer ← Db.openAt path
  let w ← writer
  let first := root "generation replacement while checkpoint fails"
  w.submit ⟨[first], true⟩
  w.save (Codec.encode (checkpoint 10))
  hideCheckpoint db
  let attempts ← IO.mkRef 0
  discard <| w.turn db fun db bytes => do
    attempts.modify (· + 1)
    try Lifecycle.save db bytes
    catch e =>
      -- A real producer may replace the checkpoint during a failed callback.
      -- The next generation is retained for a later service turn.
      w.save (Codec.encode (checkpoint 20))
      restoreCheckpoint db
      throw e
  t.ok "newer checkpoint arriving during failure is retained for the next turn"
    ((← attempts.get) == 1 && (← w.saving.get) == (2, some (Codec.encode (checkpoint 20))) &&
      (← w.saved.get) == 0 && !(← w.saveDone))
  t.ok "generation replacement cannot hold the selected signed write"
    ((← valid observer first) && (← w.count.get) == 1 && (← w.busy.get) == 0)
  discard <| w.turn db fun db bytes => do
    Lifecycle.save db bytes
    w.save (Codec.encode (checkpoint 30))
  t.ok "successful older checkpoint acknowledges only its actual generation"
    ((← w.saved.get) == 2 && (← Lifecycle.load observer) == some (checkpoint 20))
  t.ok "newer checkpoint arriving during success remains pending and unacknowledged"
    ((← w.saving.get) == (3, some (Codec.encode (checkpoint 30))) && !(← w.saveDone))
  discard <| w.turn db Lifecycle.save
  t.ok "the following actual turn commits and acknowledges the latest generation"
    ((← w.saved.get) == 3 && (← w.saving.get) == (3, none) && (← w.saveDone) &&
      (← Lifecycle.load observer) == some (checkpoint 30))

end WriterCheckpoint

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/writer-checkpoint/runtime"
  let t ← Checks.new
  WriterCheckpoint.oneAttempt t dir
  WriterCheckpoint.generations t dir
  t.finish "writer-checkpoint"
