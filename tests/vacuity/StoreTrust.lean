import tests.engine.Lib
import engine.core.SqliteLaws

/-! The store's trust file (engine/core/StoreTrust.lean), from both sides.

- **Consistent:** the model's own store keeps the contract's shape, in the
  kernel, and empty rows show the empty tables: no part is contradictory.
- **Has content:** a store that drops a write fails the shape, in the
  kernel, and rows with a queued op do not show empty tables.
- **Satisfied by the running code:** the executable opens a real SQLite
  file, brings it and the model to the same tables with a workload, and
  then runs each store operation alone on both. Each answer must be the
  model's, and the rows (the dumps) must show the model's next tables.
  It also checks beginning and committing, a refused write turn, the
  budget query, list queries and a purge's rewrite.
- **What the laws take:** `sqliteConditional` gives the contract to the
  laws over the running write turn and purge (engine/core/SqliteLaws.lean).

tests/engine/Differential.lean, QueryDiff.lean and Purge.lean test the
same contract on long random workloads. -/
namespace Vacuity.StoreTrust
open Engine Community Tests Trust
set_option linter.defProp false

/-! ## Consistent: the model keeps the shape -/

/-- The model's own store, as a store whose states are its tables. -/
def modelRun {α : Type} (op : StoreOp Unit α) (s : DB Unit) : Option (α × DB Unit) :=
  some (op.run (m := Model Unit) s)

theorem modelKeeps : AnswersAsModel (F := Unit) modelRun Eq := by
  intro α op t s hs v t' h
  subst hs
  simp only [modelRun, Option.some.injEq] at h
  rw [h]
  exact ⟨rfl, rfl⟩

theorem emptyShows : (⟨[], [], [], [], []⟩ : Rows Unit).Show DB.empty :=
  ⟨fun _ => rfl, List.Perm.nil, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩

/-! ## Has content: a store that drops a write fails it -/

def anOp : Op := Op.make 0 [] .empty

/-- A store whose `putOp` keeps nothing. -/
def dropRun {α : Type} : StoreOp Unit α → DB Unit → Option (α × DB Unit)
  | .putOp _, s => some ((), s)
  | op, s => some (op.run (m := Model Unit) s)

theorem dropRefused : ¬ AnswersAsModel (F := Unit) dropRun Eq := by
  intro h
  have := (h (.putOp anOp) DB.empty DB.empty rfl () DB.empty rfl).2
  have hops := congrArg (fun s : DB Unit => s.ops anOp.id) this
  simp [StoreOp.run, Store.putOp, DB.putOp, DB.empty] at hops

theorem queuedNotEmpty : ¬ (⟨[], [], [], [anOp.id], []⟩ : Rows Unit).Show DB.empty := by
  intro h
  have := h.2.2.2.2.1
  simp [DB.empty] at this

/-- The contract, bridged to the laws over the running write turn and
purge: what each of them takes. -/
def sqliteConditional := some (PLift.up
  (fun (holds : Db → Void IO.RealWorld → DB Fact → Prop) (t : SqliteStore Fact holds) =>
    And.intro (receive_as_model t (family ed25519) []) (purge_as_model t (family ed25519) [] false)))

/-- The contract, bridged to the refused-turn law. -/
def refusedConditional := some (PLift.up
  (fun (holds : Db → Void IO.RealWorld → DB Fact → Prop) (t : SqliteStore Fact holds) =>
    @receive_refused Fact _ holds _ t (family ed25519) []))

/-! ## Satisfied by the running code -/

/-- `Rows.Show` on finite tables: every id and key the workload names. -/
def showsOn (r : Rows Fact) (s : DB Fact) (ids : List Id) (keys : List ByteArray) : Bool :=
  r.ops.all (fun o => s.ops o.id == some o) &&
  ids.all (fun x => s.ops x == r.ops.find? (fun o => o.id == x)) &&
  s.stored.isPerm (r.ops.map (·.id)) &&
  ids.all (fun x => s.status x == (r.status.find? (fun p => p.1 == x)).map (·.2)) &&
  r.status.all (fun p => ids.contains p.1) &&
  ids.all (fun b => s.waits b == under r.waits b) &&
  r.waits.all (fun p => ids.contains p.1) &&
  s.queue == r.queue &&
  keys.all (fun k => s.idx k == under r.idx k) &&
  r.idx.all (fun p => keys.contains p.1)

def keysOf (fam : Family Fact) (s : DB Fact) (ids : List Id) : List ByteArray :=
  (ids.foldl (fun acc x => match s.status x with
    | some (.valid f) => acc ++ fam.fileKeys x f
    | _ => acc) ([] : List ByteArray)).eraseDups

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "the contract is what the running write turn and purge need" sqliteConditional.isSome
  t.ok "the contract is what the refused-turn law needs" refusedConditional.isSome
  let dir := "out/vacuity"
  IO.FS.createDirAll dir
  let path := s!"{dir}/store-trust.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  let fam := family ed25519
  let ops := workload 7 60
  let ids := (ops.map (·.id) ++ ops.flatMap (·.reqs)).eraseDups
  let rows : IO (Rows Fact) := (dump (F := Fact)).run db
  let fresh := Op.make 9 [] "an op the workload does not have".toUTF8
  let ids := ids ++ [fresh.id]
  t.ok "an opened empty file shows the empty tables" (showsOn (← rows) DB.empty ids [])
  -- Bring the file and the model to the same tables: half the workload,
  -- judged part way, so some ops wait, some are decided, some queued.
  let mut s : DB Fact := DB.empty
  db.exec "BEGIN IMMEDIATE"
  for o in ops.take 40 do
    (ingest (m := SqlM Fact) o).run db
    s := (ingest (m := Model Fact) o s).2
  for _ in [0:25] do
    let _ ← (step (m := SqlM Fact) fam).run db
    s := (step (m := Model Fact) fam s).2
  db.exec "COMMIT"
  let keys := keysOf fam s ids
  t.ok "the workload's file shows the model's tables" (showsOn (← rows) s ids keys)
  t.ok "the workload decided ops, filed facts and left some queued"
    (!keys.isEmpty && !s.queue.isEmpty && ids.any fun x => (s.status x).isSome)
  -- Each operation alone, inside a transaction rolled back afterwards.
  let one {α : Type} [BEq α] (name : String) (op : StoreOp Fact α) : IO Unit := do
    db.exec "BEGIN IMMEDIATE"
    let v ← (op.run (m := SqlM Fact)).run db
    let (v', s') := op.run (m := Model Fact) s
    let keys' := keysOf fam s' ids ++ keys
    t.ok s!"{name}: SQLite answers as the model" (v == v')
    t.ok s!"{name}: the rows show the model's next tables" (showsOn (← rows) s' ids keys'.eraseDups)
    db.exec "ROLLBACK"
    t.ok s!"{name}: rolled back, the rows show the tables before" (showsOn (← rows) s ids keys)
  let stored := ids.filter fun x => (s.ops x).isSome
  let waiting := ids.filter fun x => !(s.waits x).isEmpty
  let some x := stored.head? | throw (IO.userError "no stored op")
  let some w := waiting.head? | throw (IO.userError "no op waits")
  let some k := keys.head? | throw (IO.userError "no filing")
  let v : Verdict Fact := (s.status x).getD .invalid
  for y in stored.take 6 ++ [fresh.id] do
    one s!"getOp {hex y}" (.getOp y)
    one s!"getStatus {hex y}" (.getStatus y)
    one s!"dependents {hex y}" (.dependents y)
    one s!"waiters {hex y}" (.waiters y)
  one "putOp (new)" (.putOp fresh)
  one "setStatus" (.setStatus fresh.id v)
  one "setStatus (replace)" (.setStatus x .invalid)
  one "addWait (new)" (.addWait x fresh.id)
  one "addWait (again)" (.addWait w ((s.waits w).headD fresh.id))
  one "clearWaiters" (.clearWaiters w)
  one "push" (.push x)
  one "pop" .pop
  one "index (new)" (.index k fresh.id)
  one "index (again)" (.index k ((s.idx k).headD fresh.id))
  one "lookup" (.lookup k)
  one "undecide" (.undecide x)
  one "deleteOp" (.deleteOp x)
  one "countOps" .countOps
  -- The check has content: after a write, the rows no longer show the
  -- tables before it.
  db.exec "BEGIN IMMEDIATE"
  (Store.putOp (F := Fact) (m := SqlM Fact) fresh).run db
  t.ok "the check has content: a written op's rows do not show the tables before" (!showsOn (← rows) s ids keys)
  db.exec "ROLLBACK"
  -- Beginning and committing change no table.
  db.exec "BEGIN IMMEDIATE"
  t.ok "after BEGIN IMMEDIATE the rows show the same tables" (showsOn (← rows) s ids keys)
  db.exec "COMMIT"
  t.ok "after COMMIT the rows show the same tables" (showsOn (← rows) s ids keys)
  -- A refused write turn changes no table.
  let refused ← ((transact (do
      Store.putOp (F := Fact) (m := SqlM Fact) fresh
      Store.push (F := Fact) (m := SqlM Fact) fresh.id
      throw (IO.userError "refused") : SqlM Fact Unit)).run db).toBaseIO
  t.ok "a refused write turn fails" (match refused with | .error _ => true | .ok _ => false)
  t.ok "a refused write turn changes no table" (showsOn (← rows) s ids keys)
  -- The budget query counts the model's tables.
  db.exec "BEGIN"
  let b ← (budgetSql (F := Fact)).run db
  db.exec "COMMIT"
  t.ok s!"the budget query counts the model's tables ({b})" (b == budgetOf s)
  -- List queries answer as `eval`.
  for k' in keys.take 8 do
    for q in [{ key := k', limit := some 5 }, { key := k', limit := none, desc := false },
              ({ key := k', limit := some 0, cap := 2 } : ListQ)] do
      let a ← (listSql (F := Fact) q).run db
      t.ok s!"a list of {hex k'} answers as eval" (a == eval s q)
  t.ok "list queries change no table" (showsOn (← rows) s ids keys)
  -- A purge's rewrite changes no table.
  for vacuum in [false, true] do
    let _ ← ((scrubSql (F := Fact) vacuum).run db).toBaseIO
    t.ok s!"a purge's rewrite (vacuum {vacuum}) changes no table" (showsOn (← rows) s ids keys)
  -- A whole write turn and a purge, through the laws' code.
  (receive fam (ops.drop 40)).run db
  let turn : Model Fact Unit := discard <| turnCapped (m := Model Fact) fam drainCap (ops.drop 40)
  let s2 := (turn s).2
  let keys2 := keysOf fam s2 ids
  t.ok "a write turn's rows show the model's write turn" (showsOn (← rows) s2 ids keys2)
  purgeSql fam [x] false |>.run db
  let purged : Model Fact Unit := discard <| purgeCapped (m := Model Fact) fam drainCap [x]
  let s3 := (purged s2).2
  t.ok "a purge's rows show the model's purge" (showsOn (← rows) s3 ids (keysOf fam s3 ids))
  t.finish "store trust file: satisfied by SQLite, operation by operation"

end Vacuity.StoreTrust
