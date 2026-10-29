/- The production Reader and SQLite on large indexed communities. Facts
are seeded as already-decided rows to isolate the read path; signature,
admission, and removal validation are covered by the community suites.
The cache case runs Reader.pass and real filing triggers across commits. -/
import ops.app.Reader
import tests.engine.Checks

open Engine Community Data Tests

namespace PeopleReader

def bytes (s : String) : ByteArray := s.toUTF8

def file (db : Db) (id : String) (f : Fact) : IO Unit := do
  let sf : SF := .inl f
  (show SqlM SF Unit from do
    Store.setStatus (bytes id) (.valid sf)
    for k in fam.keys sf do Store.index k (bytes id)).run db

def add (db : Db) (c : Id) (n : Nat) (oneUser := false) : IO Unit := do
  db.exec "BEGIN IMMEDIATE"
  try
    for i in [0:n] do
      let u := if oneUser then bytes "one-user" else bytes s!"user-{i}"
      file db s!"{String.fromUTF8! c}-admission-{i}" (.admission c u (bytes s!"device-{i}") (bytes s!"node-{i}"))
    db.exec "COMMIT"
  catch e =>
    db.exec "ROLLBACK"
    throw e

def people (db : Db) (c : Id) : IO (Reader.Val × Array Q × Reader.St) := do
  let ((v, deps), s) ← (Reader.eval (.people c)).run { rd := db }
  return (v, deps, s)

def run (ck : Checks) : IO Unit := do
  let db ← openDb ":memory:"
  db.filings
  let small := bytes "small"
  add db small 2
  file db "small-another-device" (.admission small (bytes "user-0") (bytes "extra-device") (bytes "extra-node"))
  let (v, _, _) ← people db small
  ck.ok "small header is exact and deduplicates users across devices" (v == .people 2 true)
  let commits ← IO.mkRef 1
  let sh ← Reader.Shared.new commits
  sh.setWants #[.people small]
  let (_, s) ← (Reader.pass sh).run { rd := db }
  ck.ok "reader publishes the exact initial count" (((← sh.board.get).get? (.people small)).map (·.1) == some (.people 2 true))
  file db "remove-user-0" (.removal small (bytes "user-0") small)
  commits.modify (· + 1)
  let (_, s) ← (Reader.pass sh).run s
  ck.ok "removal commit invalidates cached header and cuts all user devices"
    (((← sh.board.get).get? (.people small)).map (·.1) == some (.people 1 true))
  let reads := s.live.reads
  let (_, s) ← (Reader.pass sh).run s
  ck.ok "unchanged header stays cached" (s.live.reads == reads)
  let big := bytes "large"
  add db big 1100
  let (v, deps, s) ← people db big
  ck.ok "large header reports a capped lower bound" (v == .people 999 false)
  ck.ok "header asks for only the newest 1024 admissions"
    (deps[0]? == some (.list (admission.all.query [big] (limit := some 1024))))
  ck.ok "one-admission devices keep header reads bounded independent of community size" (s.live.reads ≤ 1 + 2 * 1024)
  let ((v, _), _) ← (Reader.eval (.members big big)).run { rd := db }
  ck.ok "opened people list remains exact beyond the header cap" (match v with | .members ms _ => ms.size == 1100 | _ => false)
  let duplicates := bytes "duplicate-large"
  add db duplicates 1100 true
  let (v, _, _) ← people db duplicates
  ck.ok "incomplete scan is marked even when the visible unique count is small" (v == .people 1 false)

end PeopleReader

def main : IO UInt32 := do
  let ck ← Checks.new
  PeopleReader.run ck
  ck.finish "people-reader"
