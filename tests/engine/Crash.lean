/-
Atomicity under a hard kill. `crash write` takes a workload in batches,
one transaction each, and is killed (SIGKILL) at a random moment by
tests/crash.sh; `crash check` then opens what is on disk and requires
it to be exactly the state after some number of whole batches: the
stored ops are the first k batches, the queue is empty, and every table
equals the model's after those k batches, whose verdicts equal the
spec's.
-/
import Tests.Lib

open Engine Community Tests

def batches (seed : Nat) : List (List Op) :=
  let ops := workload seed 2000
  (List.range ((ops.length + 9) / 10)).map fun i => (ops.drop (10 * i)).take 10

def modelAfter (fam : Family Fact) (bs : List (List Op)) : DB Fact :=
  bs.foldl (fun s b =>
    let s := b.foldl (fun s o => ingestS o s) s
    drainS fam (20 * b.length + 20) s) DB.empty

def main (args : List String) : IO UInt32 := do
  let fam := family ed25519
  match args with
  | ["write", path, seed] =>
    let db ← Db.openAt path
    let bs := batches seed.toNat!
    let out ← IO.getStdout
    for b in bs, i in [0:bs.length] do
      (receive fam b).run db
      out.putStrLn s!"committed {i + 1}"
      out.flush
    return 0
  | ["check", path, seed] =>
    let t ← Checks.new
    let db ← Db.openAt path
    let bs := batches seed.toNat!
    let stored := (← (dumpOps (F := Fact)).run db).map (·.id)
    let k := (List.range (bs.length + 1)).find? fun k =>
      let ids := ((bs.take k).flatten.map (·.id))
      ids.length == stored.length && ids.all stored.contains
    match k with
    | none =>
      t.ok s!"stored ops ({stored.length}) are whole batches" false
    | some k =>
      IO.println s!"on disk: {k} of {bs.length} batches"
      let ops := (bs.take k).flatten
      let ids0 := (ops.map (·.id) ++ ops.flatMap (·.reqs)).eraseDups
      let m := modelAfter fam (bs.take k)
      sameTables t s!"after {k} batches" db m ids0
      t.ok "queue empty" m.queue.isEmpty
      t.ok "verdicts equal the spec's" (ids0.all fun x => m.status x == specOf fam m.ops ops.length x)
    t.finish "crash check"
  | _ => IO.eprintln "usage: crash write|check <db> <seed>"; return 2
