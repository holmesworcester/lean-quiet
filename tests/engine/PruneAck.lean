/- The actual production prune step and reader pass use the shared progress
refs. Signed roots generate real SQLite journal rows, then the first stale
snapshot and a second prune show whether acknowledgement survived. -/
import tests.engine.PublicationFixture
import engine.core.Exit
open Engine Data PublicationFixture

def mainBody (args : List String) : IO UInt32 := do
  let readerMode := args.contains "--reader"
  let dir := args.headD "out/ref-publications/prune"
  let (path, db) ← database dir
  let op := root "actual journal publication"
  (receive Data.fam [op] : SqlM SF Unit).run db
  unless ← valid db op do throw (IO.userError "journal fixture root must be valid")
  let (_, _, top) ← db.filingsSince 0
  unless top > 0 do throw (IO.userError "real root produced no journal rows")
  let w ← writer
  if readerMode then
    let sh ← Reader.Shared.new w.count
    armNat sh.seen
    let pass ← IO.asTask (prio := .dedicated) do
      waitRelease
      entered
      let (_, state) ← (Reader.pass sh).run { rd := ← Db.openAt path }
      done
      return state
    let before ← sh.seen.get
    let .ok state ← IO.wait pass | throw (IO.userError "actual reader pass failed")
    let seen ← sh.seen.get
    -- The reader's internal cursor has advanced. A real idle pass must not
    -- be mistaken for an acknowledgement retry that this implementation lacks.
    discard <| (Reader.pass sh).run state
    let afterIdle ← sh.seen.get
    w.noticed (min top afterIdle)
    w.pruneOnce db
    let (fs, vs, _) ← db.filingsSince 0
    let pruned := fs.isEmpty && vs.isEmpty
    if !(← injected) || before != 0 || seen != top || afterIdle != top || !pruned then
      IO.eprintln s!"FAIL: actual reader pass publishes journal progress despite the overlapping old read (before={before}, seen={seen}, top={top}, idle={afterIdle}, pruned={pruned})"
      return 1
    IO.println "reader-seen: actual reader pass publication survives SDK overlap and idle pass; real journal is pruned"
  else
    armNat w.read
    let notice ← IO.asTask (prio := .dedicated) do
      waitRelease
      entered
      w.noticed top
      done
    -- This is the exact function the production five-second prune loop calls.
    w.pruneOnce db
    let result ← IO.wait notice
    let noticed ← w.read.get
    w.pruneOnce db
    let (fs, vs, _) ← db.filingsSince 0
    let pruned := fs.isEmpty && vs.isEmpty
    if !(← injected) || !result.isOk || noticed != top || !pruned then
      IO.eprintln s!"FAIL: actual prune step retains a concurrently published journal acknowledgement (noticed={noticed}, top={top}, pruned={pruned})"
      return 1
    IO.println "prune-ack: actual production prune step observes the published progress after SDK overlap"
  unless ← valid db op do
    IO.eprintln "FAIL: journal pruning preserves the underlying valid op"
    return 1
  return 0

/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main (args : List String) : IO UInt32 := Engine.exitAfter (mainBody args)
